using System;
using System.Collections.Generic;
using System.Linq;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {
  private record QfFrameComponent(Bpl.Expr Objects, Bpl.Expr Field);
  private record QfFrameSnapshot(List<QfFrameComponent> Components, Bpl.Expr Alloc, Variables Locals);
  private readonly Dictionary<string, QfFrameSnapshot> qfFrames = new();
  private bool qfAllocSetConfigured;

  private Bpl.Expr QfAllocatedSet(IOrigin tok, Bpl.Expr alloc) {
    if (!qfAllocSetConfigured) {
      // P3 omitted the definition of this prelude conversion. It is a
      // background map operation, not an axiom quantifying over heaps.
      var conversion = sink.TopLevelDeclarations.OfType<Bpl.Function>().Single(f => f.Name == "SetRef_to_SetBox");
      var map = new Bpl.IdentifierExpr(tok, conversion.InParams[0]);
      var element = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$qfBox", Predef.BoxType));
      var boxed = new Bpl.IdentifierExpr(tok, element);
      var body = new Bpl.LambdaExpr(tok, [], [element], null,
        Bpl.Expr.Select(map, ApplyUnbox(tok, boxed, Predef.RefType)));
      conversion.Body = FunctionCall(tok, "Set#FromBoogieMap", Predef.SetType, body);
      conversion.Attributes = InlineAttribute(tok, conversion.Attributes);
      qfAllocSetConfigured = true;
    }
    return FunctionCall(tok, "SetRef_to_SetBox", Predef.SetType, alloc);
  }

  private bool SupportsQfFrame(IEnumerable<FrameExpression> expressions) => expressions.All(frame => {
    var expression = frame.E.Resolved;
    if (expression is FieldLocationExpression location) {
      expression = location.Lhs.Resolved;
    }
    return expression.Type?.NormalizeToAncestorType() is SetType { Finite: true } set && set.Arg.IsRefType ||
      expression.Type?.IsRefType == true;
  });

  private bool TryQfFrameComponents(IOrigin tok, IEnumerable<FrameExpression> expressions, ExpressionTranslator etran,
    out List<QfFrameComponent> components) {
    components = [];
    if (!SupportsQfFrame(expressions)) {
      return false;
    }
    foreach (var frame in expressions) {
      var expression = frame.E.Resolved;
      var field = frame.Field;
      if (expression is FieldLocationExpression location) {
        field = location.ResolvedField;
        expression = location.Lhs.Resolved;
      }
      var objects = expression.Type.IsRefType ? QfSingleton(tok, etran.TrExpr(expression)) : etran.TrExpr(expression);
      // Null has no heap cells and is ignored by Dafny's frame semantics.
      objects = QfSetDifference(tok, objects, QfSingleton(tok, Predef.Null));
      components.Add(new QfFrameComponent(objects, field == null ? null : new Bpl.IdentifierExpr(tok, GetField(field))));
    }
    return true;
  }

  private Bpl.Expr QfFrameObjects(IOrigin tok, IEnumerable<QfFrameComponent> components) =>
    components.Aggregate(QfEmptySet(tok), (acc, component) => QfSetUnion(tok, acc, component.Objects));

  private Bpl.Expr QfFramesDisjoint(IOrigin tok, IEnumerable<QfFrameComponent> changed,
    IEnumerable<QfFrameComponent> support) {
    Bpl.Expr result = Bpl.Expr.True;
    foreach (var change in changed) {
      foreach (var component in support) {
        var disjoint = QfSetDisjoint(tok, change.Objects, component.Objects);
        if (change.Field != null && component.Field != null) {
          disjoint = BplOr(Bpl.Expr.Neq(change.Field, component.Field), disjoint);
        }
        result = BplAnd(result, disjoint);
      }
    }
    return result;
  }

  private Bpl.Expr QfInFrame(IOrigin tok, IEnumerable<QfFrameComponent> components, Bpl.Expr obj, Bpl.Expr field) {
    Bpl.Expr result = Bpl.Expr.False;
    foreach (var component in components) {
      Bpl.Expr member = FunctionCall(tok, BuiltinFunction.SetIsMember, null, component.Objects, ApplyBox(tok, obj));
      if (component.Field != null && field != null) {
        member = BplAnd(member, Bpl.Expr.Eq(field, component.Field));
      }
      result = BplOr(result, member);
    }
    return result;
  }

  private bool TryDefineQfFrame(IOrigin tok, Bpl.IdentifierExpr identifier, List<FrameExpression> expressions,
    BoogieStmtListBuilder builder, Variables locals, string name, ExpressionTranslator etran) {
    if (!UseQuantifierFreeFrames || !TryQfFrameComponents(tok, expressions, etran, out var components)) {
      return false;
    }
    var frozen = new List<QfFrameComponent>();
    foreach (var component in components) {
      var local = locals.GetOrAdd(new Bpl.LocalVariable(tok,
        new Bpl.TypedIdent(tok, CurrentIdGenerator.FreshId("$qfFrameSet#"), Predef.SetType)));
      var objects = new Bpl.IdentifierExpr(tok, local);
      builder.Add(Bpl.Cmd.SimpleAssign(tok, objects, component.Objects));
      frozen.Add(new QfFrameComponent(objects, component.Field));
    }
    var allocLocal = locals.GetOrAdd(new Bpl.LocalVariable(tok,
      new Bpl.TypedIdent(tok, CurrentIdGenerator.FreshId("$qfFrameAlloc#"), AllocMapType(tok))));
    var alloc = new Bpl.IdentifierExpr(tok, allocLocal);
    builder.Add(Bpl.Cmd.SimpleAssign(tok, alloc, AllocStateExprForHeapExpr(tok, etran.HeapExpr)));
    qfFrames[name ?? identifier.Name] = new QfFrameSnapshot(frozen, alloc, locals);
    return true;
  }

  private Bpl.Expr FrameMembership(IOrigin tok, Bpl.IdentifierExpr frame, Bpl.Expr obj, Bpl.Expr field) {
    if (UseQuantifierFreeFrames && qfFrames.TryGetValue(frame.Name, out var snapshot)) {
      return BplOr(Bpl.Expr.Not(BplAnd(Bpl.Expr.Neq(obj, Predef.Null), Bpl.Expr.Select(snapshot.Alloc, obj))),
        QfInFrame(tok, snapshot.Components, obj, field));
    }
    return Bpl.Expr.SelectTok(tok, frame, obj, field);
  }

  private bool TryQfFrameSubset(IOrigin tok, List<FrameExpression> calleeFrame, Expression receiver,
    Dictionary<IVariable, Expression> substitutions, ExpressionTranslator etran, Bpl.IdentifierExpr enclosingFrame,
    Action<IOrigin, Bpl.Expr, ProofObligationDescription, Bpl.QKeyValue> makeAssert,
    Action<IOrigin, Bpl.Expr> makeAssume, ProofObligationDescription description, Bpl.QKeyValue attributes) {
    if (!UseQuantifierFreeFrames || !qfFrames.TryGetValue(enclosingFrame.Name, out var frame)) {
      return false;
    }
    foreach (var expression in calleeFrame) {
      var substituted = substitutions == null ? expression.E : Substitute(expression.E, receiver, substitutions);
      makeAssume(expression.Origin, etran.CanCallAssumption(substituted));
    }
    // Unassigned, unconstrained implementation locals denote arbitrary values.
    // Unlike a map lambda/forall, this introduces no quantified heap encoding.
    var objLocal = frame.Locals.GetOrAdd(new Bpl.LocalVariable(tok,
      new Bpl.TypedIdent(tok, CurrentIdGenerator.FreshId("$qfSubsetObject#"), Predef.RefType)));
    var fieldLocal = frame.Locals.GetOrAdd(new Bpl.LocalVariable(tok,
      new Bpl.TypedIdent(tok, CurrentIdGenerator.FreshId("$qfSubsetField#"), Predef.FieldName(tok))));
    var obj = new Bpl.IdentifierExpr(tok, objLocal);
    var field = new Bpl.IdentifierExpr(tok, fieldLocal);
    var ante = BplAnd(BplAnd(Bpl.Expr.Neq(obj, Predef.Null), etran.IsAlloced(tok, obj)),
      InRWClause(tok, obj, field, calleeFrame, etran, receiver, substitutions));
    makeAssert(tok, BplImp(ante, FrameMembership(tok, enclosingFrame, obj, field)), description, attributes);
    return true;
  }

  private bool QfExpressionInScope(Expression expression, Variables locals) {
    if (expression is OldExpr or ComprehensionExpr or LetExpr) {
      return false;
    }
    if (expression is IdentifierExpr identifier) {
      return identifier.Var is Formal || identifier.Var is LocalVariable local &&
        locals.GetValueOrDefault(local.AssignUniqueName(CurrentDeclaration.IdGenerator)) != null;
    }
    return expression.SubExpressions.All(sub => QfExpressionInScope(sub.Resolved, locals));
  }

  private List<Expression> QfRelevantExpressions(Variables locals, IEnumerable<Expression> extra = null) {
    var expressions = new List<Expression>();
    if (codeContext is MethodOrFunction member) {
      expressions.AddRange(member.Req.Select(req => req.E));
      expressions.AddRange(member.Ens.Select(ens => ens.E));
      expressions.AddRange(member.Decreases.Expressions);
    }
    if (codeContext is MethodOrConstructor { Body: { } body }) {
      expressions.AddRange(body.SubExpressionsIncludingTransitiveSubStatements);
    }
    if (extra != null) {
      expressions.AddRange(extra);
    }
    // Filter individual ground terms after traversal. Filtering a whole
    // postcondition would discard its current-state terms merely because a
    // different conjunct contains old(...), a quantifier, or a let binding.
    return expressions.Select(expression => expression.Resolved).ToList();
  }

  private Dictionary<IVariable, Expression> QfFunctionSubstitutions(FunctionCallExpr call) {
    var substitutions = new Dictionary<IVariable, Expression>();
    var typeSubstitutions = call.GetTypeArgumentSubstitutions();
    for (var i = 0; i < call.Args.Count; i++) {
      var type = call.Function.Ins[i].Type.Subst(typeSubstitutions);
      substitutions.Add(call.Function.Ins[i], new BoxingCastExpr(call.Args[i], call.Args[i].Type, type) { Type = type });
    }
    return substitutions;
  }

  private Expression QfFunctionBody(FunctionCallExpr call) =>
    Substitute(call.Function.Body, call.Receiver, QfFunctionSubstitutions(call), call.GetTypeArgumentSubstitutions(), call.AtLabel);

  private List<FrameExpression> QfFunctionReadExpressions(FunctionCallExpr call) {
    var substitutions = QfFunctionSubstitutions(call);
    return call.Function.Reads.Expressions.Select(frame => new FrameExpression(frame.Origin,
      Substitute(frame.E, call.Receiver, substitutions, call.GetTypeArgumentSubstitutions()), frame.FieldName) { Field = frame.Field }).ToList();
  }

  private void CollectQfTerms(Expression expression, List<FunctionCallExpr> calls, List<Expression> reads, List<Expression> references,
    HashSet<Function> active) {
    expression = expression.Resolved;
    if (expression is OldExpr or ComprehensionExpr or LetExpr) {
      return;
    }
    if (expression.Type?.IsRefType == true) {
      references.Add(expression);
    }
    if (expression is FunctionCallExpr call) {
      calls.Add(call);
      // Discovery only. Full function support comes from reads, never from a
      // depth-capped traversal of a recursive body. Inline nonrecursive wrappers
      // to discover terms such as List(this.head) inside Valid().
      if (active.Add(call.Function)) {
        foreach (var frame in QfFunctionReadExpressions(call)) {
          CollectQfTerms(frame.E, calls, reads, references, active);
        }
        if (call.Function.Body != null && !call.Function.IsRecursive) {
          CollectQfTerms(QfFunctionBody(call), calls, reads, references, active);
        }
        active.Remove(call.Function);
      }
    }
    if (expression is MemberSelectExpr { Member: Field { IsMutable: true } } ||
        expression is SeqSelectExpr { SelectOne: true } selection && selection.Seq.Type.IsArrayType ||
        expression is MultiSelectExpr) {
      reads.Add(expression);
    }
    foreach (var sub in expression.SubExpressions) {
      CollectQfTerms(sub, calls, reads, references, active);
    }
  }

  private FunctionCallExpr QfCallWithArguments(FunctionCallExpr call, Expression receiver, List<Expression> arguments) =>
    new(call.Origin, call.NameNode, receiver, call.OpenParen, call.CloseParen, arguments, call.AtLabel) {
      Function = call.Function, Type = call.Type,
      TypeApplication_AtEnclosingClass = call.TypeApplication_AtEnclosingClass,
      TypeApplication_JustFunction = call.TypeApplication_JustFunction
    };

  private FunctionCallExpr FreezeQfArguments(FunctionCallExpr call, ExpressionTranslator etran) =>
    QfCallWithArguments(call,
      call.Function.IsStatic ? call.Receiver : new BoogieWrapper(etran.TrExpr(call.Receiver), call.Receiver.Type),
      call.Args.Select(arg => (Expression)new BoogieWrapper(etran.TrExpr(arg), arg.Type)).ToList());

  private IEnumerable<FunctionCallExpr> QfFrameInstances(FunctionCallExpr call, List<Expression> references) {
    // Artifact add_instantiation_pairs: substitute foreground arguments with
    // current variables and pointer projections. Background arguments stay fixed.
    IEnumerable<Expression> Choices(Expression original, Type acceptedType) => acceptedType.IsRefType
      ? references.Where(reference => reference.Type.IsSubtypeOf(acceptedType, false, false)).Prepend(original)
      : new[] { original };
    IEnumerable<List<Expression>> Arguments(int index) {
      if (index == call.Args.Count) {
        yield return [];
      } else {
        foreach (var argument in Choices(call.Args[index], call.Function.Ins[index].Type.Subst(call.GetTypeArgumentSubstitutions()))) {
          foreach (var tail in Arguments(index + 1)) {
            yield return tail.Prepend(argument).ToList();
          }
        }
      }
    }
    IEnumerable<Expression> receivers = call.Function.IsStatic ? new[] { call.Receiver } : Choices(call.Receiver, call.Receiver.Type);
    foreach (var receiver in receivers) {
      foreach (var arguments in Arguments(0)) {
        yield return QfCallWithArguments(call, receiver, arguments);
      }
    }
  }

  private List<QfFrameComponent> QfFunctionSupport(FunctionCallExpr call, ExpressionTranslator etran) {
    var frames = QfFunctionReadExpressions(call);
    return TryQfFrameComponents(call.Origin, frames, etran, out var components) ? components : null;
  }

  private Bpl.Expr QfCallWellFormed(FunctionCallExpr call, ExpressionTranslator etran) {
    // A newly discovered term need not have a #canCall assumption in the old
    // state. Use the actual domain conditions, including the preconditions.
    // In particular, total opaque functions can be framed at null.
    var substitutions = QfFunctionSubstitutions(call);
    Bpl.Expr result = Bpl.Expr.True;
    foreach (var require in call.Function.Req) {
      var precondition = Substitute(require.E, call.Receiver, substitutions, call.GetTypeArgumentSubstitutions());
      result = BplAnd(result, etran.CanCallAssumption(precondition));
      result = BplAnd(result, etran.TrExpr(precondition));
    }
    if (!call.Function.IsStatic && call.Receiver.Type.IsRefType) {
      result = BplAnd(result, Bpl.Expr.Neq(etran.TrExpr(call.Receiver), Predef.Null));
      result = BplAnd(result, MkIs(etran.TrExpr(call.Receiver), call.Receiver.Type));
    }
    foreach (var argument in call.Args) {
      var typeFact = GetWhereClause(argument.Origin, etran.TrExpr(argument), argument.Type, etran, NOALLOC);
      if (typeFact != null) {
        result = BplAnd(result, typeFact);
      }
    }
    return result;
  }

  private Bpl.Expr QfCallAllocated(FunctionCallExpr call, ExpressionTranslator etran) {
    var result = QfCallWellFormed(call, etran);
    IEnumerable<Expression> arguments = call.Function.IsStatic ? call.Args : call.Args.Prepend(call.Receiver);
    foreach (var argument in arguments) {
      var allocated = GetWhereClause(argument.Origin, etran.TrExpr(argument), argument.Type, etran, ISALLOC, true);
      if (allocated != null) {
        result = BplAnd(result, allocated);
      }
    }
    return result;
  }

  private List<Bpl.PredicateCmd> QfTransitionFacts(IOrigin tok, Variables locals, ExpressionTranslator before,
    ExpressionTranslator after, List<QfFrameComponent> modified, IEnumerable<Expression> expressions,
    bool canAllocate, IEnumerable<Bpl.Expr> extraModified = null) {
    var calls = new List<FunctionCallExpr>();
    var reads = new List<Expression>();
    var references = new List<Expression>();
    foreach (var expression in expressions) {
      CollectQfTerms(expression, calls, reads, references, new HashSet<Function>());
    }
    calls = calls.Where(call => QfExpressionInScope(call, locals))
      .DistinctBy(call => before.TrExpr(call).ToString()).ToList();
    references = references.Where(reference => QfExpressionInScope(reference, locals))
      .DistinctBy(reference => before.TrExpr(reference).ToString()).ToList();
    var variables = references.Where(reference => reference is IdentifierExpr or ThisExpr or BoogieWrapper).ToList();
    var pointers = reads.OfType<MemberSelectExpr>().Where(read => read.Type.IsRefType).ToList();
    foreach (var variable in variables) {
      foreach (var pointer in pointers.Where(pointer => variable.Type.IsSubtypeOf(pointer.Obj.Type, false, false))) {
        references.Add(new MemberSelectExpr(pointer.Origin, variable, pointer.MemberNameNode) {
          Member = pointer.Member, Type = pointer.Type,
          TypeApplicationAtEnclosingClass = pointer.TypeApplicationAtEnclosingClass,
          TypeApplicationJustMember = pointer.TypeApplicationJustMember
        });
      }
    }
    references = references.DistinctBy(reference => before.TrExpr(reference).ToString()).ToList();
    var instances = calls.SelectMany(call => QfFrameInstances(call, references))
      .DistinctBy(call => before.TrExpr(call).ToString()).ToList();
    foreach (var instance in instances) {
      CollectQfTerms(instance, calls, reads, references, new HashSet<Function>());
    }
    calls = calls.Where(call => QfExpressionInScope(call, locals))
      .DistinctBy(call => before.TrExpr(call).ToString()).ToList();
    reads = reads.Where(read => QfExpressionInScope(read, locals))
      .DistinctBy(read => before.TrExpr(read).ToString()).ToList();
    var changes = new List<QfFrameComponent>(modified);
    foreach (var obj in extraModified ?? []) {
      changes.Add(new QfFrameComponent(QfSingleton(tok, obj), null));
    }
    var beforeAlloc = AllocStateExprForHeapExpr(tok, before.HeapExpr);
    var afterAlloc = AllocStateExprForHeapExpr(tok, after.HeapExpr);
    if (canAllocate) {
      changes.Add(new QfFrameComponent(QfSetDifference(tok, QfAllocatedSet(tok, afterAlloc), QfAllocatedSet(tok, beforeAlloc)), null));
    }
    var facts = new List<Bpl.PredicateCmd>();
    var seen = new HashSet<string>();
    void Assume(Bpl.Expr fact) {
      if (seen.Add(fact.ToString())) {
        facts.Add(TrAssumeCmd(tok, fact));
      }
    }
    if (canAllocate) {
      Assume(QfSetSubset(tok, QfAllocatedSet(tok, beforeAlloc), QfAllocatedSet(tok, afterAlloc)));
    } else {
      Assume(Bpl.Expr.Eq(beforeAlloc, afterAlloc));
    }
    foreach (var call in calls.Where(call => call.Function is not TwoStateFunction && call.AtLabel == null)) {
      foreach (var state in new[] { before, after }) {
        // Ground counterpart of the allocation consequence axiom, which is
        // omitted in QF mode because it would capture the global $Alloc.
        var valid = QfCallAllocated(call, state);
        var resultType = GetWhereClause(tok, state.TrExpr(call), call.Type, state, ISALLOC);
        if (resultType != null) {
          Assume(BplImp(valid, resultType));
        }
        AddQfSetFacts(call, state, fact => Assume(BplImp(valid, fact)));
      }
    }
    // Instantiate on both pre- and post-state projections. Each equality uses
    // the SAME argument values on its two sides (the cloud operator in §5.1).
    foreach (var call in calls.Where(call => call.Function.ReadsHeap && call.Function is not TwoStateFunction &&
               !call.Function.ReadsDoubleStar && call.AtLabel == null)) {
      foreach (var argumentState in new[] { before, after }) {
        var frozen = FreezeQfArguments(call, argumentState);
        var support = QfFunctionSupport(frozen, before);
        if (support == null) {
          continue;
        }
        var ante = BplAnd(QfCallWellFormed(frozen, before), QfFramesDisjoint(tok, changes, support));
        Assume(BplImp(ante, Bpl.Expr.Eq(before.TrExpr(frozen), after.TrExpr(frozen))));
        // Supports themselves are functions of the heap and must be framed too.
        var postSupport = QfFunctionSupport(frozen, after);
        if (postSupport != null) {
          Assume(BplImp(ante, QfSetEqual(tok, QfFrameObjects(tok, support), QfFrameObjects(tok, postSupport))));
        }
      }
    }
    foreach (var read in reads) {
      // Reconstruct the ground instances of Dafny's good-heap typing axioms.
      // A call may allocate, but it must still return a well-typed heap.
      if (read is MemberSelectExpr { Member: Field } memberRead) {
        foreach (var state in new[] { before, after }) {
          var receiver = state.TrExpr(memberRead.Obj);
          var value = state.TrExpr(memberRead);
          var receiverValid = BplAnd(BplAnd(Bpl.Expr.Neq(receiver, Predef.Null), state.IsAlloced(tok, receiver)),
            MkIs(receiver, memberRead.Obj.Type));
          var typeFact = GetWhereClause(tok, value, memberRead.Type, state, ISALLOC);
          if (typeFact != null) {
            Assume(BplImp(receiverValid, typeFact));
          }
          AddQfSetFacts(memberRead, state, fact => Assume(BplImp(receiverValid, fact)));
        }
      }
      foreach (var argumentState in new[] { before, after }) {
        Bpl.Expr obj;
        Bpl.Expr field;
        if (read is MemberSelectExpr member && member.Member is Field mutable) {
          obj = argumentState.TrExpr(member.Obj);
          field = new Bpl.IdentifierExpr(tok, GetField(mutable));
        } else if (read is SeqSelectExpr selection) {
          obj = argumentState.TrExpr(selection.Seq);
          field = FunctionCall(tok, BuiltinFunction.IndexField, null,
            ConvertExpression(tok, argumentState.TrExpr(selection.E0), selection.E0.Type, Type.Int));
        } else if (read is MultiSelectExpr multi) {
          obj = argumentState.TrExpr(multi.Array);
          field = argumentState.GetArrayIndexFieldName(tok, multi.Indices);
        } else {
          continue;
        }
        var ante = BplAnd(Bpl.Expr.Neq(obj, Predef.Null), Bpl.Expr.Not(QfInFrame(tok, modified, obj, field)));
        if (canAllocate) {
          ante = BplAnd(ante, Bpl.Expr.Select(beforeAlloc, obj));
        }
        foreach (var changed in extraModified ?? []) {
          ante = BplAnd(ante, Bpl.Expr.Neq(obj, changed));
        }
        Assume(BplImp(ante, Bpl.Expr.Eq(ReadHeap(tok, before.HeapExpr, obj, field), ReadHeap(tok, after.HeapExpr, obj, field))));
      }
    }
    return facts;
  }

  private Bpl.Expr QfSetAllocated(IOrigin tok, Bpl.Expr set, Bpl.Expr heap) =>
    QfSetSubset(tok, QfSetDifference(tok, set, QfSingleton(tok, Predef.Null)),
      QfAllocatedSet(tok, AllocStateExprForHeapExpr(tok, heap)));

  private Bpl.IdentifierExpr SnapshotQfHeap(IOrigin tok, string prefix, Variables locals,
    BoogieStmtListBuilder builder, ExpressionTranslator etran) {
    var name = CurrentIdGenerator.FreshId(prefix);
    var local = locals.GetOrAdd(new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, name, Predef.HeapType)));
    var heap = new Bpl.IdentifierExpr(tok, local);
    builder.Add(Bpl.Cmd.SimpleAssign(tok, heap, etran.HeapExpr));
    SnapshotAllocState(tok, name, locals, builder, etran);
    return heap;
  }

  private void EmitQfMutationFacts(IOrigin tok, Bpl.IdentifierExpr preHeap, Bpl.Expr obj, Bpl.Expr field,
    BoogieStmtListBuilder builder, Variables locals, ExpressionTranslator etran) {
    if (preHeap == null) {
      return;
    }
    var before = new ExpressionTranslator(etran, preHeap);
    var modified = new List<QfFrameComponent> { new(QfSingleton(tok, obj), field) };
    builder.Add(new Bpl.CommentCmd("qf-mutation-frame: full reads supports"));
    foreach (var fact in QfTransitionFacts(tok, locals, before, etran, modified, QfRelevantExpressions(locals), false)) {
      builder.Add(fact);
    }
  }
}
