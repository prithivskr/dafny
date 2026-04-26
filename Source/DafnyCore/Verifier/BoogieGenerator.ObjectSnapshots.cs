using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {
  public class ObjectFieldSnapshotState {
    readonly BoogieGenerator boogieGenerator;
    readonly Dictionary<Field, Bpl.Function> fieldSnapshots;
    Bpl.Function allocationSnapshot;
    int snapshotVersion;

    public ObjectFieldSnapshotState(BoogieGenerator boogieGenerator, Bpl.Expr legacyHeap)
      : this(boogieGenerator, legacyHeap, new Dictionary<Field, Bpl.Function>(), null) {
    }

    ObjectFieldSnapshotState(BoogieGenerator boogieGenerator, Bpl.Expr legacyHeap,
      Dictionary<Field, Bpl.Function> fieldSnapshots, Bpl.Function allocationSnapshot) {
      this.boogieGenerator = boogieGenerator;
      LegacyHeap = legacyHeap;
      this.fieldSnapshots = fieldSnapshots;
      this.allocationSnapshot = allocationSnapshot;
      snapshotVersion = 0;
    }

    public Bpl.Expr LegacyHeap { get; }
    public int SnapshotVersion => snapshotVersion;

    public ObjectFieldSnapshotState Clone(Bpl.Expr legacyHeap) {
      return new ObjectFieldSnapshotState(boogieGenerator, legacyHeap, new Dictionary<Field, Bpl.Function>(fieldSnapshots), allocationSnapshot) {
        snapshotVersion = this.snapshotVersion
      };
    }

    public Bpl.Expr ReadField(IOrigin tok, Field field, Bpl.Expr receiver) {
      Contract.Requires(field != null);
      Contract.Requires(field.IsMutable);
      Contract.Requires(receiver != null);
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
}
