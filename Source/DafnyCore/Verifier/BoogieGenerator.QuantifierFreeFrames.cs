using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {
  private record HeapRead(Bpl.Expr Receiver, Bpl.Expr Field, string ReceiverKey, string FieldKey);

  private bool UseQuantifierFreeFrames => options.Get(CommonOptionBag.QuantifierFreeFrames);

  // Depth cap for recursive unfolding in ComputeBoundedSupport
  private const int QfSupportUnfoldDepth = 3;

  private Bpl.Type AllocMapType(Bpl.IToken tok) {
    return new Bpl.MapType(tok, [], [Predef.RefType], Bpl.Type.Bool);
  }

  internal string AllocVariableNameFromHeapName(string heapVariableName) {
    if (heapVariableName.Contains("$Heap", StringComparison.Ordinal)) {
      return heapVariableName.Replace("$Heap", "$Alloc", StringComparison.Ordinal);
    }
    if (heapVariableName.Contains("$heap", StringComparison.Ordinal)) {
      return heapVariableName.Replace("$heap", "$alloc", StringComparison.Ordinal);
    }
    return "$Alloc";
  }

  internal Bpl.IdentifierExpr AllocStateIdentifierExpr(Bpl.IToken tok, string allocVariableName = "$Alloc") {
    return new Bpl.IdentifierExpr(tok, allocVariableName, AllocMapType(tok));
  }

  internal void AddQfAllocToModifiesList(Bpl.IToken tok, List<Bpl.IdentifierExpr> modifies) {
    if (!UseQuantifierFreeFrames) {
      return;
    }
    modifies.Add(AllocStateIdentifierExpr(tok));
  }

  internal Bpl.Expr AllocStateExprForHeapExpr(Bpl.IToken tok, Bpl.Expr heapExpr) {
    if (!UseQuantifierFreeFrames) {
      return null;
    }
    return heapExpr switch {
      Bpl.OldExpr oldExpr => new Bpl.OldExpr(tok, AllocStateExprForHeapExpr(tok, oldExpr.Expr)),
      Bpl.IdentifierExpr identifierExpr when identifierExpr.Name.Contains("Alloc", StringComparison.Ordinal) ||
                                             identifierExpr.Name.Contains("alloc", StringComparison.Ordinal)
        => identifierExpr,
      Bpl.IdentifierExpr identifierExpr when identifierExpr.Name.Contains("$Heap", StringComparison.Ordinal) ||
                                             identifierExpr.Name.Contains("$heap", StringComparison.Ordinal)
        => AllocStateIdentifierExpr(tok, AllocVariableNameFromHeapName(identifierExpr.Name)),
      _ => AllocStateIdentifierExpr(tok)
    };
  }

  internal Bpl.IdentifierExpr SnapshotAllocState(IOrigin tok, string heapVariableName, Variables locals,
    BoogieStmtListBuilder builder, ExpressionTranslator etran) {
    var allocVariableName = AllocVariableNameFromHeapName(heapVariableName);
    var allocVar = locals.GetOrAdd(new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, allocVariableName, AllocMapType(tok))));
    var allocIdentifier = new Bpl.IdentifierExpr(tok, allocVar);
    builder.Add(Bpl.Cmd.SimpleAssign(tok, allocIdentifier, AllocStateExprForHeapExpr(tok, etran.HeapExpr)));
    return allocIdentifier;
  }

  private bool NeedsLegacyModifiesFrame(IEnumerable<FrameExpression> frameExpressions, ExpressionTranslator etran) {
    return !UseQuantifierFreeFrames || !TryCollectConcreteModifiedRefs(frameExpressions, etran, out _);
  }

  private bool IsFrameConditionBoilerplate(BoilerplateTriple triple) {
    return triple.Comment != null && triple.Comment.StartsWith("frame condition", StringComparison.Ordinal);
  }

  private string ExprKey(Bpl.Expr expr) {
    Contract.Requires(expr != null);
    return expr.ToString();
  }

  private bool SameBoogieExpr(Bpl.Expr a, Bpl.Expr b) {
    return ExprKey(a) == ExprKey(b);
  }

  private IEnumerable<Field> RelevantFieldsForQfFrame(IEnumerable<HeapRead> reads) {
    var seen = new HashSet<string>();
    foreach (var read in reads) {
      if (FieldExprToField(read.Field) is { } field && seen.Add(field.FullSanitizedName)) {
        yield return field;
      }
    }
  }

  private Field FieldExprToField(Bpl.Expr fieldExpr) {
    if (fieldExpr is Bpl.IdentifierExpr identifierExpr) {
      return fields.FirstOrDefault(pair => pair.Value.Name == identifierExpr.Name).Key;
    }
    return null;
  }

  private List<HeapRead> CollectHeapReads(params Bpl.Expr[] exprs) {
    var result = new Dictionary<string, HeapRead>();
    foreach (var expr in exprs.Where(expr => expr != null)) {
      CollectHeapReads(expr, result);
    }
    return result.Values.ToList();
  }

  private void CollectHeapReads(Bpl.Expr expr, Dictionary<string, HeapRead> result) {
    switch (expr) {
      case Bpl.NAryExpr nAryExpr:
        if (nAryExpr.Fun is Bpl.FunctionCall functionCall &&
            functionCall.FunctionName == "read" &&
            nAryExpr.Args.Count == 3) {
          var receiver = nAryExpr.Args[1];
          var field = nAryExpr.Args[2];
          var heapRead = new HeapRead(receiver, field, ExprKey(receiver), ExprKey(field));
          result.TryAdd($"{heapRead.ReceiverKey}::{heapRead.FieldKey}", heapRead);
        }
        foreach (var arg in nAryExpr.Args) {
          CollectHeapReads(arg, result);
        }
        break;
      case Bpl.OldExpr oldExpr:
        CollectHeapReads(oldExpr.Expr, result);
        break;
    }
  }

  private List<Bpl.Expr> CollectSupport(Bpl.Expr expr) {
    var result = new Dictionary<string, Bpl.Expr>();
    CollectSupport(expr, result);
    return result.Values.ToList();
  }

  private void CollectSupport(Bpl.Expr expr, Dictionary<string, Bpl.Expr> result) {
    switch (expr) {
      case Bpl.NAryExpr nAryExpr:
        if (nAryExpr.Fun is Bpl.FunctionCall functionCall &&
            functionCall.FunctionName == "read" &&
            nAryExpr.Args.Count == 3) {
          var receiver = nAryExpr.Args[1];
          result.TryAdd(ExprKey(receiver), receiver);
          CollectSupport(receiver, result);
          CollectSupport(nAryExpr.Args[2], result);
          CollectSupport(nAryExpr.Args[0], result);
          return;
        }
        foreach (var arg in nAryExpr.Args) {
          CollectSupport(arg, result);
        }
        break;
      case Bpl.OldExpr oldExpr:
        CollectSupport(oldExpr.Expr, result);
        break;
    }
  }

  private List<Bpl.Expr> CollectLiveRefs(Variables locals, ExpressionTranslator etran, IEnumerable<Bpl.Expr> relevantExpressions) {
    var result = new Dictionary<string, Bpl.Expr>();

    if (codeContext is MethodOrFunction methodOrFunction) {
      foreach (var parameter in methodOrFunction.Ins.Where(parameter => parameter.Type.IsRefType)) {
        var expr = TrVar(parameter.Origin, parameter);
        result.TryAdd(ExprKey(expr), expr);
      }
    }
    if (codeContext is Method method) {
      foreach (var parameter in method.Outs.Where(parameter => parameter.Type.IsRefType)) {
        var expr = TrVar(parameter.Origin, parameter);
        result.TryAdd(ExprKey(expr), expr);
      }
    }

    foreach (var local in locals.Values.OfType<Bpl.Variable>().Where(local => local.TypedIdent.Type.Equals(Predef.RefType))) {
      var expr = new Bpl.IdentifierExpr(local.tok, local);
      result.TryAdd(ExprKey(expr), expr);
    }

    foreach (var expr in relevantExpressions.Where(expr => expr != null)) {
      foreach (var supportExpr in CollectSupport(expr).Where(supportExpr => supportExpr.Type != null && supportExpr.Type.Equals(Predef.RefType))) {
        result.TryAdd(ExprKey(supportExpr), supportExpr);
      }
    }

    return result.Values.ToList();
  }

  private void ComputeBoundedSupport(Expression expr, ExpressionTranslator etran, int depthBudget,
    Dictionary<string, HeapRead> accumulator, Dictionary<string, bool> callMemo) {
    if (expr == null) {
      return;
    }

    switch (expr) {
      case MemberSelectExpr memberSelect when memberSelect.Member is Field { IsMutable: true } field: {
          // Sp(e.f) = {(tr(e), tr(f))} ∪ Sp(e)
          var receiverBpl = etran.TrExpr(memberSelect.Obj);
          var fieldBpl = new Bpl.IdentifierExpr(field.Origin, GetField(field));
          var heapRead = new HeapRead(receiverBpl, fieldBpl, ExprKey(receiverBpl), ExprKey(fieldBpl));
          accumulator.TryAdd($"{heapRead.ReceiverKey}::{heapRead.FieldKey}", heapRead);

          // Recurse into the receiver to capture its own support (e.g. x.next.val records x.next too)
          ComputeBoundedSupport(memberSelect.Obj, etran, depthBudget, accumulator, callMemo);
          break;
        }

      case SeqSelectExpr seqSelect when seqSelect.SelectOne: {
          // Array/sequence element read: treat the sequence as the "receiver" and the index
          // expression translated as the "field" key.

          if (seqSelect.E0 != null) {
            var seqBpl = etran.TrExpr(seqSelect.Seq);
            var idxBpl = etran.TrExpr(seqSelect.E0);
            var heapRead = new HeapRead(seqBpl, idxBpl, ExprKey(seqBpl), ExprKey(idxBpl));
            accumulator.TryAdd($"{heapRead.ReceiverKey}::{heapRead.FieldKey}", heapRead);
          }
          ComputeBoundedSupport(seqSelect.Seq, etran, depthBudget, accumulator, callMemo);
          if (seqSelect.E0 != null) {
            ComputeBoundedSupport(seqSelect.E0, etran, depthBudget, accumulator, callMemo);
          }
          if (seqSelect.E1 != null) {
            ComputeBoundedSupport(seqSelect.E1, etran, depthBudget, accumulator, callMemo);
          }
          break;
        }

      case FunctionCallExpr funcCall when funcCall.Function?.Body != null: {
          var func = funcCall.Function;

          var argKey = string.Join(",", funcCall.Args.Select(a => etran.TrExpr(a).ToString()));
          var memoKey = $"{func.FullSanitizedName}|{argKey}|{depthBudget}";
          if (!callMemo.TryAdd(memoKey, true)) {
            break;
          }

          bool isRecursive = func.IsRecursive;
          if (isRecursive && depthBudget <= 0) {
            break;
          }

          // Substitute actual arguments into the function body
          var substMap = new Dictionary<IVariable, Expression>();
          Contract.Assert(funcCall.Args.Count == func.Ins.Count);

          for (int i = 0; i < func.Ins.Count; i++) {
            var formal = func.Ins[i];
            var formalType = formal.Type.Subst(funcCall.GetTypeArgumentSubstitutions());
            Expression arg = funcCall.Args[i];
            arg = new BoxingCastExpr(arg, arg.Type, formalType);
            arg.Type = formalType;
            substMap.Add(formal, arg);
          }

          var substitutedBody = Substitute(func.Body, funcCall.Receiver, substMap,
            funcCall.GetTypeArgumentSubstitutions(), funcCall.AtLabel);

          int nextBudget = isRecursive ? depthBudget - 1 : depthBudget;
          ComputeBoundedSupport(substitutedBody, etran, nextBudget, accumulator, callMemo);
          break;
        }

      default: {
          // Recurse structurally into sub-expressions without consuming depth budget.
          foreach (var sub in expr.SubExpressions) {
            ComputeBoundedSupport(sub, etran, depthBudget, accumulator, callMemo);
          }
          break;
        }
    }
  }

  /// <summary>
  /// Convenience wrapper: computes bounded support for a collection of Dafny expressions and
  /// returns the deduplicated set of heap reads discovered.
  /// </summary>
  private List<HeapRead> ComputeBoundedSupportForExprs(IEnumerable<Expression> dafnyExprs, ExpressionTranslator etran) {
    var accumulator = new Dictionary<string, HeapRead>();
    var callMemo = new Dictionary<string, bool>();
    foreach (var expr in dafnyExprs.Where(e => e != null)) {
      ComputeBoundedSupport(expr, etran, QfSupportUnfoldDepth, accumulator, callMemo);
    }
    return accumulator.Values.ToList();
  }

  /// <summary>
  /// Cross-product <paramref name="liveRefs"/> with every distinct mutable field and every
  /// array-like (non-named-field) entry found in <paramref name="supportReads"/>, adding the
  /// resulting pairs into <paramref name="result"/>
  /// </summary>
  private void ExpandSupportWithLiveRefs(IEnumerable<Bpl.Expr> liveRefs,
    IEnumerable<HeapRead> supportReads, Dictionary<string, HeapRead> result) {
    var reads = supportReads.ToList();

    // Seed result with the directly-discovered reads.
    foreach (var read in reads) {
      result.TryAdd($"{read.ReceiverKey}::{read.FieldKey}", read);
    }

    // Determine the distinct fields (named and array-like) seen in the support.
    var namedFields = RelevantFieldsForQfFrame(reads).Where(f => f.IsMutable).ToList();
    var arrayLikeFields = reads
      .Where(r => FieldExprToField(r.Field) == null)
      .Select(r => r.Field)
      .GroupBy(ExprKey)
      .Select(g => g.First())
      .ToList();

    // Emit one fact per (liveRef, field) pair so the verifier can reason about any live ref
    foreach (var liveRef in liveRefs.Where(r => r.Type != null && r.Type.Equals(Predef.RefType))) {
      foreach (var field in namedFields) {
        var fieldExpr = new Bpl.IdentifierExpr(field.Origin, GetField(field));
        var hr = new HeapRead(liveRef, fieldExpr, ExprKey(liveRef), ExprKey(fieldExpr));
        result.TryAdd($"{hr.ReceiverKey}::{hr.FieldKey}", hr);
      }
      foreach (var fieldExpr in arrayLikeFields) {
        var hr = new HeapRead(liveRef, fieldExpr, ExprKey(liveRef), ExprKey(fieldExpr));
        result.TryAdd($"{hr.ReceiverKey}::{hr.FieldKey}", hr);
      }
    }
  }

  private bool TryCollectConcreteModifiedRefs(IEnumerable<FrameExpression> frameExpressions, ExpressionTranslator etran, out List<Bpl.Expr> modifiedRefs) {
    modifiedRefs = [];
    foreach (var frameExpression in frameExpressions) {
      if (frameExpression.FieldName != null) {
        modifiedRefs = [];
        return false;
      }
      if (!TryCollectConcreteModifiedRefs(frameExpression.E, etran, modifiedRefs)) {
        modifiedRefs = [];
        return false;
      }
    }
    return true;
  }

  private bool TryCollectConcreteModifiedRefs(IEnumerable<FrameExpression> frameExpressions, Expression receiverReplacement,
    Dictionary<IVariable, Expression> substMap, ExpressionTranslator etran, out List<Bpl.Expr> modifiedRefs) {
    modifiedRefs = [];
    foreach (var frameExpression in frameExpressions) {
      if (frameExpression.FieldName != null) {
        modifiedRefs = [];
        return false;
      }
      var e = substMap != null ? Substitute(frameExpression.E, receiverReplacement, substMap) : frameExpression.E;
      if (!TryCollectConcreteModifiedRefs(e, etran, modifiedRefs)) {
        modifiedRefs = [];
        return false;
      }
    }
    return true;
  }

  private bool TryCollectConcreteModifiedRefs(Expression expr, ExpressionTranslator etran, List<Bpl.Expr> modifiedRefs) {
    switch (expr) {
      case SetDisplayExpr setDisplayExpr:
        return setDisplayExpr.Elements.All(element => TryCollectConcreteModifiedRefs(element, etran, modifiedRefs));
      case ThisExpr when codeContext is not MemberDecl { IsStatic: false }:
        return false;
      default:
        if (expr.Type == null || !expr.Type.IsRefType) {
          return false;
        }
        return AddModifiedRef(modifiedRefs, etran.TrExpr(expr));
    }
  }

  private bool AddModifiedRef(List<Bpl.Expr> modifiedRefs, Bpl.Expr refExpr) {
    if (!modifiedRefs.Any(existing => SameBoogieExpr(existing, refExpr))) {
      modifiedRefs.Add(refExpr);
    }
    return true;
  }

  private Bpl.Expr ConcreteFootprintMembership(IOrigin tok, Bpl.Expr obj, IEnumerable<Bpl.Expr> footprint) {
    var refs = footprint.ToList();
    if (refs.Count == 0) {
      return Bpl.Expr.False;
    }
    return refs
      .Select(modifiedRef => Bpl.Expr.Eq(obj, modifiedRef))
      .Aggregate((Bpl.Expr)Bpl.Expr.False, (acc, expr) => BplOr(acc, expr));
  }

  private bool IsSyntacticConcreteFootprintMember(Bpl.Expr obj, IEnumerable<Bpl.Expr> footprint) {
    return footprint.Any(modifiedRef => SameBoogieExpr(obj, modifiedRef));
  }

  private Bpl.Expr ConcreteFootprintOrFreshPermission(IOrigin tok, Bpl.Expr obj, IEnumerable<Bpl.Expr> footprint, ExpressionTranslator etran,
    Bpl.Expr allocSnapshot = null) {
    var inFootprint = ConcreteFootprintMembership(tok, obj, footprint);
    var isFreshSinceEntry = allocSnapshot == null
      ? Bpl.Expr.Not(etran.Old.IsAlloced(tok, obj))
      : Bpl.Expr.Not(IsAlloced(tok, allocSnapshot, obj));
    return BplOr(inFootprint, isFreshSinceEntry);
  }

  private bool TryEmitConcreteModifiesCheck(IOrigin tok, Bpl.Expr obj, IEnumerable<FrameExpression> frameExpressions,
    ExpressionTranslator etran, BoogieStmtListBuilder builder, ProofObligationDescription desc) {
    if (!UseQuantifierFreeFrames || !TryCollectConcreteModifiedRefs(frameExpressions, etran, out var footprint)) {
      return false;
    }
    if (IsSyntacticConcreteFootprintMember(obj, footprint)) {
      return true;
    }
    builder.Add(Assert(tok, ConcreteFootprintMembership(tok, obj, footprint), desc, builder.Context));
    return true;
  }

  private bool TryEmitConcreteFrameSubset(IOrigin tok, IEnumerable<FrameExpression> frameExpressions,
    IEnumerable<FrameExpression> enclosingFrameExpressions, Expression receiverReplacement, Dictionary<IVariable, Expression> substMap,
    ExpressionTranslator etran, BoogieStmtListBuilder builder, ProofObligationDescription desc, Bpl.QKeyValue kv,
    Bpl.Expr allocSnapshot = null) {
    if (!UseQuantifierFreeFrames) {
      return false;
    }
    if (!TryCollectConcreteModifiedRefs(frameExpressions, receiverReplacement, substMap, etran, out var calleeFootprint) ||
        !TryCollectConcreteModifiedRefs(enclosingFrameExpressions, etran, out var enclosingFootprint)) {
      return false;
    }

    foreach (var frameExpression in frameExpressions) {
      var e = substMap != null ? Substitute(frameExpression.E, receiverReplacement, substMap) : frameExpression.E;
      builder.Add(TrAssumeCmd(frameExpression.Origin, etran.CanCallAssumption(e)));
    }

    foreach (var calleeRef in calleeFootprint) {
      if (IsSyntacticConcreteFootprintMember(calleeRef, enclosingFootprint)) {
        continue;
      }
      builder.Add(Assert(tok, ConcreteFootprintOrFreshPermission(tok, calleeRef, enclosingFootprint, etran, allocSnapshot), desc, builder.Context, kv));
    }
    return true;
  }

  private List<Bpl.PredicateCmd> BuildQfFrameFactCommands(IOrigin tok,
    Bpl.Expr preHeap, ExpressionTranslator etran, IEnumerable<Bpl.Expr> liveRefs, IEnumerable<HeapRead> reads, IEnumerable<Bpl.Expr> modifiedRefs) {
    var readList = reads.ToList();
    var modifiedList = modifiedRefs.ToList();
    var emitted = new HashSet<string>();
    var commands = new List<Bpl.PredicateCmd>();

    if (!readList.Any()) {
      return commands;
    }
    foreach (var read in readList) {
      var key = $"{read.ReceiverKey}::{read.FieldKey}";
      if (!emitted.Add(key)) {
        continue;
      }

      var equality = Bpl.Expr.Eq(
        ReadHeap(tok, etran.HeapExpr, read.Receiver, read.Field),
        ReadHeap(tok, preHeap, read.Receiver, read.Field));

      Bpl.Expr ante = Bpl.Expr.Neq(read.Receiver, Predef.Null);
      foreach (var modifiedRef in modifiedList) {
        ante = BplAnd(ante, Bpl.Expr.Neq(read.Receiver, modifiedRef));
      }

      commands.Add(TrAssumeCmd(tok, BplImp(ante, equality)));
    }
    return commands;
  }

  private bool TryBuildLoopQfFrameFacts(IOrigin tok, LoopStmt loop, Expression guard, Variables locals,
    Bpl.Expr preLoopHeap, ExpressionTranslator etran, out List<Bpl.PredicateCmd> commands) {
    commands = [];
    List<FrameExpression> effectiveModifiesClause;
    if (loop.Mod.Expressions != null) {
      effectiveModifiesClause = loop.Mod.Expressions;
    } else if (codeContext is IMethodCodeContext methodCodeContext) {
      effectiveModifiesClause = methodCodeContext.Modifies.Expressions;
      if (codeContext is IteratorDecl iter) {
        effectiveModifiesClause = [
          new FrameExpression(loop.Origin, new ThisExpr(iter), null),
          .. effectiveModifiesClause
        ];
      }
    } else {
      return false;
    }
    if (!TryCollectConcreteModifiedRefs(effectiveModifiesClause, etran, out var modifiedRefs)) {
      return false;
    }

    // Collect Dafny-level expressions from loop invariants and the guard.
    var dafnyRelevantExprs = new List<Expression>();
    dafnyRelevantExprs.AddRange(loop.Invariants.Select(inv => inv.E));
    if (guard != null) {
      dafnyRelevantExprs.Add(guard);
    }

    // Translate to Boogie for liveRefs seeding (still needed for alloc-freshness checks).
    var relevantBoogieExprs = dafnyRelevantExprs
      .Where(e => e != null)
      .Select(e => etran.TrExpr(e))
      .ToList();

    // Compute the bounded support from Dafny-level expressions to discover which fields are
    // relevant, then expand with liveRefs to cover every live reference-typed variable.
    var boundedSupport = ComputeBoundedSupportForExprs(dafnyRelevantExprs, etran);
    var liveRefs = CollectLiveRefs(locals, etran, relevantBoogieExprs);
    var closure = new Dictionary<string, HeapRead>();
    ExpandSupportWithLiveRefs(liveRefs, boundedSupport, closure);

    commands = BuildQfFrameFactCommands(tok, preLoopHeap, etran, liveRefs, closure.Values, modifiedRefs);
    return true;
  }

  private void EmitCallQfFrameFacts(IOrigin tok, CallStmt callStmt, BoogieStmtListBuilder builder, Variables locals,
    Bpl.Expr preCallHeap, ExpressionTranslator etran, IEnumerable<FrameExpression> frameExpressions,
    IEnumerable<Bpl.Expr> relevantExprs, IEnumerable<Bpl.Expr> extraModifiedRefs = null,
    IEnumerable<Expression> dafnyRelevantExprs = null) {
    if (!TryCollectConcreteModifiedRefs(frameExpressions, etran, out var modifiedRefs)) {
      return;
    }
    if (extraModifiedRefs != null) {
      foreach (var extraModifiedRef in extraModifiedRefs) {
        AddModifiedRef(modifiedRefs, extraModifiedRef);
      }
    }

    var relevantExprList = relevantExprs.Where(expr => expr != null).ToList();
    var liveRefs = CollectLiveRefs(locals, etran, relevantExprList);

    IEnumerable<HeapRead> baseReads;
    if (dafnyRelevantExprs != null) {
      var boundedSupport = ComputeBoundedSupportForExprs(dafnyRelevantExprs, etran);
      // Merge in any heap reads visible only in the already-translated Boogie expressions

      var boogieReads = CollectHeapReads(relevantExprList.ToArray());
      var merged = new Dictionary<string, HeapRead>(
        boundedSupport.ToDictionary(r => $"{r.ReceiverKey}::{r.FieldKey}"));
      foreach (var r in boogieReads) {
        merged.TryAdd($"{r.ReceiverKey}::{r.FieldKey}", r);
      }
      baseReads = merged.Values;
    } else {
      baseReads = CollectHeapReads(relevantExprList.ToArray());
    }

    var closure = new Dictionary<string, HeapRead>();
    ExpandSupportWithLiveRefs(liveRefs, baseReads, closure);

    builder.Add(new Bpl.CommentCmd($"qf-call-frame {callStmt.Method.Name}: supports={liveRefs.Count} reads={closure.Count} modified={modifiedRefs.Count}"));
    foreach (var command in BuildQfFrameFactCommands(tok, preCallHeap, etran, liveRefs, closure.Values, modifiedRefs)) {
      builder.Add(command);
    }
  }
}
