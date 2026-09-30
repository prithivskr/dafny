using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {
  private bool UseQuantifierFreeFrames => options.Get(CommonOptionBag.QuantifierFreeFrames);

  private Bpl.Type AllocMapType(Bpl.IToken tok) {
    return new Bpl.MapType(tok, [], [Predef.RefType], Bpl.Type.Bool);
  }

  internal string AllocVariableNameFromHeapName(string heapVariableName) {
    if (heapVariableName.Contains("Heap", StringComparison.Ordinal)) {
      return heapVariableName.Replace("Heap", "Alloc", StringComparison.Ordinal);
    }
    if (heapVariableName.Contains("heap", StringComparison.Ordinal)) {
      return heapVariableName.Replace("heap", "alloc", StringComparison.Ordinal);
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
      Bpl.IdentifierExpr identifierExpr when identifierExpr.Name.Contains("Heap", StringComparison.Ordinal) ||
                                             identifierExpr.Name.Contains("heap", StringComparison.Ordinal)
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
    return !UseQuantifierFreeFrames || !SupportsQfFrame(frameExpressions);
  }

  private bool IsQuantifiedFrameConditionBoilerplate(BoilerplateTriple triple) {
    // Preserve whole-heap equality for contexts that cannot allocate and have
    // an empty modifies clause. This equality is already quantifier-free.
    return triple.Expr is Bpl.ForallExpr && triple.Comment != null &&
      triple.Comment.StartsWith("frame condition", StringComparison.Ordinal);
  }

  private bool TryBuildLoopQfFrameFacts(IOrigin tok, LoopStmt loop, Expression guard, Variables locals,
    Bpl.Expr preLoopHeap, ExpressionTranslator etran, out List<Bpl.PredicateCmd> commands) {
    commands = [];
    if (!qfFrames.TryGetValue(etran.modifiesFrame, out var frame)) {
      return false;
    }
    var before = new ExpressionTranslator(etran, preLoopHeap);
    var extra = loop.Invariants.Select(invariant => invariant.E).ToList();
    if (guard != null) {
      extra.Add(guard);
    }
    commands = QfTransitionFacts(tok, locals, before, etran, frame.Components,
      QfRelevantExpressions(locals, extra), codeContext.AllowsAllocation);
    return true;
  }

  private void EmitCallQfFrameFacts(IOrigin tok, CallStmt callStmt, BoogieStmtListBuilder builder, Variables locals,
    Bpl.Expr preCallHeap, ExpressionTranslator etran, IEnumerable<FrameExpression> frameExpressions,
    IEnumerable<Bpl.Expr> extraModifiedRefs = null,
    IEnumerable<Expression> dafnyRelevantExprs = null) {
    var before = new ExpressionTranslator(etran, preCallHeap);
    if (!TryQfFrameComponents(tok, frameExpressions, before, out var components)) {
      return;
    }
    builder.Add(new Bpl.CommentCmd($"qf-call-frame {callStmt.Method.Name}: full reads supports"));
    foreach (var fact in QfTransitionFacts(tok, locals, before, etran, components,
               QfRelevantExpressions(locals, dafnyRelevantExprs), callStmt.Method.AllowsAllocation, extraModifiedRefs)) {
      builder.Add(fact);
    }
  }
}
