using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {
  private record HeapRead(Bpl.Expr Receiver, Bpl.Expr Field, string ReceiverKey, string FieldKey);

  private bool UseQuantifierFreeFrames => options.Get(CommonOptionBag.QuantifierFreeFrames);

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

  private List<HeapRead> ComputeDereferenceClosure(IEnumerable<Bpl.Expr> liveRefs, IEnumerable<HeapRead> relevantReads) {
    var reads = relevantReads.ToList();
    var result = new Dictionary<string, HeapRead>();

    foreach (var read in reads) {
      result.TryAdd($"{read.ReceiverKey}::{read.FieldKey}", read);
    }

    var fields = RelevantFieldsForQfFrame(reads).Where(field => field.IsMutable).ToList();
    var arrayLikeFields = reads.Where(read => FieldExprToField(read.Field) == null).Select(read => read.Field).ToList();
    foreach (var liveRef in liveRefs.Where(liveRef => liveRef.Type != null && liveRef.Type.Equals(Predef.RefType))) {
      foreach (var field in fields) {
        var fieldExpr = new Bpl.IdentifierExpr(field.Origin, GetField(field));
        var heapRead = new HeapRead(liveRef, fieldExpr, ExprKey(liveRef), ExprKey(fieldExpr));
        result.TryAdd($"{heapRead.ReceiverKey}::{heapRead.FieldKey}", heapRead);
      }
      foreach (var fieldExpr in arrayLikeFields) {
        var heapRead = new HeapRead(liveRef, fieldExpr, ExprKey(liveRef), ExprKey(fieldExpr));
        result.TryAdd($"{heapRead.ReceiverKey}::{heapRead.FieldKey}", heapRead);
      }
    }

    return result.Values.ToList();
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

  private bool TryEmitConcreteModifiesCheck(IOrigin tok, Bpl.Expr obj, IEnumerable<FrameExpression> frameExpressions,
    ExpressionTranslator etran, BoogieStmtListBuilder builder, ProofObligationDescription desc) {
    if (!UseQuantifierFreeFrames || !TryCollectConcreteModifiedRefs(frameExpressions, etran, out var footprint)) {
      return false;
    }
    builder.Add(Assert(tok, ConcreteFootprintMembership(tok, obj, footprint), desc, builder.Context));
    return true;
  }

  private bool TryEmitConcreteFrameSubset(IOrigin tok, IEnumerable<FrameExpression> frameExpressions,
    IEnumerable<FrameExpression> enclosingFrameExpressions, Expression receiverReplacement, Dictionary<IVariable, Expression> substMap,
    ExpressionTranslator etran, BoogieStmtListBuilder builder, ProofObligationDescription desc, Bpl.QKeyValue kv) {
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
      builder.Add(Assert(tok, ConcreteFootprintMembership(tok, calleeRef, enclosingFootprint), desc, builder.Context, kv));
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
    if (loop.Mod.Expressions == null) {
      return false;
    }
    if (!TryCollectConcreteModifiedRefs(loop.Mod.Expressions, etran, out var modifiedRefs)) {
      return false;
    }

    var relevantExprs = new List<Bpl.Expr>();
    relevantExprs.AddRange(loop.Invariants.Select(inv => etran.TrExpr(inv.E)));
    if (guard != null) {
      relevantExprs.Add(etran.TrExpr(guard));
    }

    var relevantReads = CollectHeapReads(relevantExprs.ToArray());
    var liveRefs = CollectLiveRefs(locals, etran, relevantExprs);
    var closure = ComputeDereferenceClosure(liveRefs, relevantReads);

    commands = BuildQfFrameFactCommands(tok, preLoopHeap, etran, liveRefs, closure, modifiedRefs);
    return true;
  }

  private void EmitCallQfFrameFacts(IOrigin tok, CallStmt callStmt, BoogieStmtListBuilder builder, Variables locals,
    Bpl.Expr preCallHeap, ExpressionTranslator etran, IEnumerable<FrameExpression> frameExpressions,
    IEnumerable<Bpl.Expr> relevantExprs) {
    if (!TryCollectConcreteModifiedRefs(frameExpressions, etran, out var modifiedRefs)) {
      return;
    }

    var relevantExprList = relevantExprs.Where(expr => expr != null).ToList();
    var relevantReads = CollectHeapReads(relevantExprList.ToArray());
    var liveRefs = CollectLiveRefs(locals, etran, relevantExprList);
    var closure = ComputeDereferenceClosure(liveRefs, relevantReads);

    builder.Add(new Bpl.CommentCmd($"qf-call-frame {callStmt.Method.Name}: supports={liveRefs.Count} reads={closure.Count} modified={modifiedRefs.Count}"));
    foreach (var command in BuildQfFrameFactCommands(tok, preCallHeap, etran, liveRefs, closure, modifiedRefs)) {
      builder.Add(command);
    }
  }
}
