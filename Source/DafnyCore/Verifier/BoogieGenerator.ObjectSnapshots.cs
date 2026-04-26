using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {
  public class ObjectFieldSnapshotState {
    readonly BoogieGenerator boogieGenerator;
    readonly Dictionary<Field, Bpl.Function> fieldSnapshots;
    readonly Dictionary<Field, Bpl.Expr> fieldSnapshotMaps;
    Bpl.Function allocationSnapshot;
    int snapshotVersion;

    public ObjectFieldSnapshotState(BoogieGenerator boogieGenerator, Bpl.Expr legacyHeap)
      : this(boogieGenerator, legacyHeap, new Dictionary<Field, Bpl.Function>(), new Dictionary<Field, Bpl.Expr>(), null) {
    }

    ObjectFieldSnapshotState(BoogieGenerator boogieGenerator, Bpl.Expr legacyHeap,
      Dictionary<Field, Bpl.Function> fieldSnapshots, Dictionary<Field, Bpl.Expr> fieldSnapshotMaps,
      Bpl.Function allocationSnapshot) {
      this.boogieGenerator = boogieGenerator;
      LegacyHeap = legacyHeap;
      this.fieldSnapshots = fieldSnapshots;
      this.fieldSnapshotMaps = fieldSnapshotMaps;
      this.allocationSnapshot = allocationSnapshot;
      snapshotVersion = 0;
    }

    public Bpl.Expr LegacyHeap { get; }
    public int SnapshotVersion => snapshotVersion;
    public bool IsBaseState => snapshotVersion == 0;

    public string SupportFunctionSnapshotKey {
      get {
        if (IsBaseState) {
          return "";
        }

        var parts = fieldSnapshots
          .OrderBy(kv => kv.Key.FullSanitizedName)
          .Select(kv => $"{kv.Key.FullSanitizedName}={kv.Value.Name}")
          .ToList();
        if (allocationSnapshot != null) {
          parts.Add($"alloc={allocationSnapshot.Name}");
        }
        return string.Join(";", parts);
      }
    }

    public ObjectFieldSnapshotState Clone(Bpl.Expr legacyHeap) {
      return new ObjectFieldSnapshotState(boogieGenerator, legacyHeap, new Dictionary<Field, Bpl.Function>(fieldSnapshots),
        new Dictionary<Field, Bpl.Expr>(fieldSnapshotMaps), allocationSnapshot) {
        snapshotVersion = this.snapshotVersion
      };
    }

    public ObjectFieldSnapshotState WithSupportSnapshotMaps(Dictionary<Field, Bpl.Expr> supportSnapshotMaps, Bpl.Expr legacyHeap) {
      var result = Clone(legacyHeap);
      foreach (var (field, snapshotMap) in supportSnapshotMaps) {
        result.fieldSnapshotMaps[field] = snapshotMap;
      }

      return result;
    }

    public Bpl.Expr GetFieldSnapshotMap(IOrigin tok, Field field) {
      Contract.Requires(field != null);
      Contract.Requires(field.IsMutable);
      if (fieldSnapshotMaps.TryGetValue(field, out var snapshotMap)) {
        return snapshotMap;
      }

      Contract.Assert(LegacyHeap != null);
      return boogieGenerator.ApplyHeapFieldSnapshotMap(tok, field, LegacyHeap);
    }

    public Bpl.Expr ReadField(IOrigin tok, Field field, Bpl.Expr receiver) {
      Contract.Requires(field != null);
      Contract.Requires(field.IsMutable);
      Contract.Requires(receiver != null);
      if (fieldSnapshotMaps.TryGetValue(field, out var snapshotMap)) {
        return boogieGenerator.ApplySnapshotMap(tok, snapshotMap, receiver);
      }

      return fieldSnapshots.TryGetValue(field, out var snapshot)
        ? boogieGenerator.ApplyUnarySnapshot(tok, snapshot, receiver)
        : boogieGenerator.ReadHeap(tok, LegacyHeap, receiver, new Bpl.IdentifierExpr(tok, boogieGenerator.GetField(field)));
    }

    public Bpl.Expr ReadAlloc(IOrigin tok, Bpl.Expr receiver) {
      Contract.Requires(receiver != null);
      return allocationSnapshot != null
        ? boogieGenerator.ApplyUnarySnapshot(tok, allocationSnapshot, receiver)
        : boogieGenerator.ReadHeap(tok, LegacyHeap, receiver, boogieGenerator.Predef.Alloc(tok));
    }

    public void UpdateField(IOrigin tok, Field field, Bpl.Expr receiver, Bpl.Expr boxedValue, BoogieStmtListBuilder builder) {
      Contract.Requires(field != null);
      Contract.Requires(field.IsMutable);
      Contract.Requires(receiver != null);
      Contract.Requires(boxedValue != null);
      Contract.Requires(builder != null);

      Bpl.Expr PreviousValue(Bpl.Expr arg) {
        return fieldSnapshots.TryGetValue(field, out var previous)
          ? boogieGenerator.ApplyUnarySnapshot(tok, previous, arg)
          : boogieGenerator.ReadHeap(tok, LegacyHeap, arg, new Bpl.IdentifierExpr(tok, boogieGenerator.GetField(field)));
      }

      var next = boogieGenerator.CreateUnarySnapshotFunction(tok, $"$FieldSnapshot${field.FullSanitizedName}$");
      boogieGenerator.EmitUnarySnapshotUpdateAssumptions(tok, next, PreviousValue, receiver, boxedValue, builder);
      fieldSnapshots[field] = next;

      Bpl.Expr PreviousMapValue(Bpl.Expr arg) {
        return boogieGenerator.ApplySnapshotMap(tok, GetFieldSnapshotMap(tok, field), arg);
      }

      var nextMapConst = boogieGenerator.CreateSnapshotMapConstant(tok, $"$FieldSnapshotMap${field.FullSanitizedName}$");
      var nextMap = new Bpl.IdentifierExpr(tok, nextMapConst);
      boogieGenerator.EmitSnapshotMapUpdateAssumptions(tok, nextMap, PreviousMapValue, receiver, boxedValue, builder);
      fieldSnapshotMaps[field] = nextMap;
      snapshotVersion++;
    }

    public void MarkAllocated(IOrigin tok, Bpl.Expr receiver, BoogieStmtListBuilder builder) {
      Contract.Requires(receiver != null);
      Contract.Requires(builder != null);

      Bpl.Expr PreviousValue(Bpl.Expr arg) {
        return allocationSnapshot != null
          ? boogieGenerator.ApplyUnarySnapshot(tok, allocationSnapshot, arg)
          : boogieGenerator.ReadHeap(tok, LegacyHeap, arg, boogieGenerator.Predef.Alloc(tok));
      }

      var next = boogieGenerator.CreateUnarySnapshotFunction(tok, "$AllocSnapshot$");
      boogieGenerator.EmitUnarySnapshotUpdateAssumptions(tok, next, PreviousValue, receiver, boogieGenerator.ApplyBox(tok, Bpl.Expr.True), builder);
      allocationSnapshot = next;
      snapshotVersion++;
    }
  }

  public ObjectFieldSnapshotState CreateObjectFieldSnapshotState(Bpl.Expr legacyHeap) {
    return legacyHeap == null ? null : new ObjectFieldSnapshotState(this, legacyHeap);
  }

  Bpl.Function CreateUnarySnapshotFunction(IOrigin tok, string prefix) {
    var name = topLevelSnapshotIdGenerator.FreshId(prefix);
    var formals = new List<Bpl.Variable> {
      new Bpl.Formal(tok, new Bpl.TypedIdent(tok, "arg", Predef.RefType), true)
    };
    var result = new Bpl.Formal(tok, new Bpl.TypedIdent(tok, Bpl.TypedIdent.NoName, Predef.BoxType), false);
    var function = new Bpl.Function(tok, name, [], formals, result, null, null);
    sink.AddTopLevelDeclaration(function);
    return function;
  }

  Bpl.Expr ApplyUnarySnapshot(IOrigin tok, Bpl.Function function, Bpl.Expr argument) {
    return new Bpl.NAryExpr(tok, new Bpl.FunctionCall(function),
      new List<Bpl.Expr> { argument }) {
      Type = Predef.BoxType
    };
  }

  Bpl.Type SnapshotMapType(IOrigin tok) {
    return new Bpl.MapType(tok, [], [Predef.RefType], Predef.BoxType);
  }

  Bpl.Expr ApplySnapshotMap(IOrigin tok, Bpl.Expr snapshotMap, Bpl.Expr argument) {
    return new Bpl.NAryExpr(tok, new Bpl.MapSelect(tok, 1),
      new List<Bpl.Expr> { snapshotMap, argument }) {
      Type = Predef.BoxType
    };
  }

  Bpl.Constant CreateSnapshotMapConstant(IOrigin tok, string prefix) {
    var name = topLevelSnapshotIdGenerator.FreshId(prefix);
    var constant = new Bpl.Constant(tok, new Bpl.TypedIdent(tok, name, SnapshotMapType(tok)), false);
    sink.AddTopLevelDeclaration(constant);
    return constant;
  }

  Bpl.Expr ApplyHeapFieldSnapshotMap(IOrigin tok, Field field, Bpl.Expr heap) {
    var function = GetOrCreateHeapFieldSnapshotMapFunction(field);
    return new Bpl.NAryExpr(tok, new Bpl.FunctionCall(function), new List<Bpl.Expr> { heap }) {
      Type = SnapshotMapType(tok)
    };
  }

  string GetSupportSnapshotMapFormalName(Field field) {
    Contract.Requires(field != null);
    return $"$snap_{field.FullSanitizedName}";
  }

  Bpl.Function GetOrCreateHeapFieldSnapshotMapFunction(Field field) {
    Contract.Requires(field != null);
    Contract.Requires(field.IsMutable);
    if (heapFieldSnapshotMapFunctions.TryGetValue(field, out var existing)) {
      return existing;
    }

    var tok = field.Origin;
    var heapFormal = new Bpl.Formal(tok, new Bpl.TypedIdent(tok, "heap", Predef.HeapType), true);
    var result = new Bpl.Formal(tok, new Bpl.TypedIdent(tok, Bpl.TypedIdent.NoName, SnapshotMapType(tok)), false);
    var function = new Bpl.Function(tok, $"HeapFieldSnapshotMap${field.FullSanitizedName}", [], [heapFormal], result, null, null);
    heapFieldSnapshotMapFunctions[field] = function;
    sink.AddTopLevelDeclaration(function);

    var rVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "r", Predef.RefType));
    var r = new Bpl.IdentifierExpr(tok, rVar);
    var heap = new Bpl.IdentifierExpr(tok, heapFormal);
    var mapExpr = ApplyHeapFieldSnapshotMap(tok, field, heap);
    var lhs = ApplySnapshotMap(tok, mapExpr, r);
    var rhs = ReadHeap(tok, heap, r, new Bpl.IdentifierExpr(tok, GetField(field)));
    var trigger = new Bpl.Trigger(tok, true, new List<Bpl.Expr> { lhs });
    sink.AddTopLevelDeclaration(new Bpl.Axiom(tok, new Bpl.ForallExpr(tok, [], new List<Variable> { rVar }, null, trigger,
      Bpl.Expr.Eq(lhs, rhs))));
    return function;
  }

  void EmitUnarySnapshotUpdateAssumptions(IOrigin tok, Bpl.Function next, System.Func<Bpl.Expr, Bpl.Expr> previousValueFactory,
    Bpl.Expr receiver, Bpl.Expr boxedValue, BoogieStmtListBuilder builder) {
    var argVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "arg", Predef.RefType));
    var arg = new Bpl.IdentifierExpr(tok, argVar);
    var lhs = ApplyUnarySnapshot(tok, next, arg);
    var previousValue = previousValueFactory(arg);
    var trigger = new Bpl.Trigger(tok, true, new List<Bpl.Expr> { lhs });

    var equalCase = BplImp(Bpl.Expr.Eq(arg, receiver), Bpl.Expr.Eq(lhs, boxedValue));
    builder.Add(TrAssumeCmd(tok, new Bpl.ForallExpr(tok, [], new List<Variable> { argVar }, null, trigger, equalCase)));

    var distinctCase = BplImp(Bpl.Expr.Neq(arg, receiver), Bpl.Expr.Eq(lhs, previousValue));
    builder.Add(TrAssumeCmd(tok, new Bpl.ForallExpr(tok, [], new List<Variable> { argVar }, null, trigger, distinctCase)));
  }

  void EmitSnapshotMapUpdateAssumptions(IOrigin tok, Bpl.Expr nextMap, System.Func<Bpl.Expr, Bpl.Expr> previousValueFactory,
    Bpl.Expr receiver, Bpl.Expr boxedValue, BoogieStmtListBuilder builder) {
    var argVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "arg", Predef.RefType));
    var arg = new Bpl.IdentifierExpr(tok, argVar);
    var lhs = ApplySnapshotMap(tok, nextMap, arg);
    var previousValue = previousValueFactory(arg);
    var trigger = new Bpl.Trigger(tok, true, new List<Bpl.Expr> { lhs });

    var equalCase = BplImp(Bpl.Expr.Eq(arg, receiver), Bpl.Expr.Eq(lhs, boxedValue));
    builder.Add(TrAssumeCmd(tok, new Bpl.ForallExpr(tok, [], new List<Variable> { argVar }, null, trigger, equalCase)));

    var distinctCase = BplImp(Bpl.Expr.Neq(arg, receiver), Bpl.Expr.Eq(lhs, previousValue));
    builder.Add(TrAssumeCmd(tok, new Bpl.ForallExpr(tok, [], new List<Variable> { argVar }, null, trigger, distinctCase)));
  }
}
