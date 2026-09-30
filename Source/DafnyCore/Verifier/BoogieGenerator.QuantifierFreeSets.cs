using System;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {
  private Bpl.Expr QfIte(IOrigin tok, Bpl.Expr condition, Bpl.Expr thenExpr, Bpl.Expr elseExpr) =>
    new Bpl.NAryExpr(tok, new Bpl.IfThenElse(tok), [condition, thenExpr, elseExpr]);

  private Bpl.Expr QfEmptySet(IOrigin tok) => FunctionCall(tok, BuiltinFunction.SetEmpty, Predef.BoxType);

  private Bpl.Expr QfSetEqual(IOrigin tok, Bpl.Expr a, Bpl.Expr b) =>
    FunctionCall(tok, BuiltinFunction.SetEqual, null, a, b);

  private Bpl.Expr QfSetUnion(IOrigin tok, Bpl.Expr a, Bpl.Expr b) =>
    FunctionCall(tok, BuiltinFunction.SetUnion, Predef.BoxType, a, b);

  private Bpl.Expr QfSetIntersection(IOrigin tok, Bpl.Expr a, Bpl.Expr b) =>
    FunctionCall(tok, BuiltinFunction.SetIntersection, Predef.BoxType, a, b);

  private Bpl.Expr QfSetDifference(IOrigin tok, Bpl.Expr a, Bpl.Expr b) =>
    FunctionCall(tok, BuiltinFunction.SetDifference, Predef.BoxType, a, b);

  private Bpl.Expr QfSetSubset(IOrigin tok, Bpl.Expr a, Bpl.Expr b) =>
    QfSetEqual(tok, QfSetDifference(tok, a, b), QfEmptySet(tok));

  private Bpl.Expr QfSetDisjoint(IOrigin tok, Bpl.Expr a, Bpl.Expr b) =>
    QfSetEqual(tok, QfSetIntersection(tok, a, b), QfEmptySet(tok));

  private Bpl.Expr QfSingleton(IOrigin tok, Bpl.Expr obj) =>
    FunctionCall(tok, BuiltinFunction.SetUnionOne, Predef.BoxType, QfEmptySet(tok), ApplyBox(tok, obj));

  // P3 represents sets by unrestricted Boogie maps. Do not globally assert the
  // finite-set cardinality laws for every map: infinite maps also inhabit that
  // sort. Instantiate them only for well-formed Dafny expressions of finite
  // set type, just as natural proofs instantiates the background theory locally.
  private void EmitQfSetFacts(Expression expression, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
    AddQfSetFacts(expression, etran, fact => builder.Add(TrAssumeCmd(expression.Origin, fact)));
  }

  private void AddQfSetFacts(Expression expression, ExpressionTranslator etran, Action<Bpl.Expr> emit) {
    if (!UseQuantifierFreeFrames || !options.Get(CommonOptionBag.Prelude3)) {
      return;
    }
    var tok = expression.Origin;
    Bpl.Expr Card(Bpl.Expr s) => FunctionCall(tok, BuiltinFunction.SetCard, null, s);
    void Assume(Bpl.Expr fact) => emit(fact);
    void Finite(Bpl.Expr s) {
      Assume(Bpl.Expr.Le(Bpl.Expr.Literal(0), Card(s)));
      Assume(Bpl.Expr.Iff(Bpl.Expr.Eq(Card(s), Bpl.Expr.Literal(0)), QfSetEqual(tok, s, QfEmptySet(tok))));
    }

    if (expression.Type?.NormalizeToAncestorType() is SetType { Finite: true }) {
      var s = etran.TrExpr(expression);
      Finite(s);
      if (expression is SetDisplayExpr display) {
        var prefix = QfEmptySet(tok);
        Assume(Bpl.Expr.Eq(Card(prefix), Bpl.Expr.Literal(0)));
        foreach (var element in display.Elements) {
          var boxed = etran.BoxIfNecessary(tok, etran.TrExpr(element), element.Type);
          var next = FunctionCall(tok, BuiltinFunction.SetUnionOne, Predef.BoxType, prefix, boxed);
          var member = FunctionCall(tok, BuiltinFunction.SetIsMember, null, prefix, boxed);
          Assume(Bpl.Expr.Eq(Card(next), Bpl.Expr.Add(Card(prefix), QfIte(tok, member,
            Bpl.Expr.Literal(0), Bpl.Expr.Literal(1)))));
          prefix = next;
        }
      } else if (expression is BinaryExpr binary && binary.E0.Type.NormalizeToAncestorType() is SetType { Finite: true } &&
                 binary.E1.Type.NormalizeToAncestorType() is SetType { Finite: true }) {
        var a = etran.TrExpr(binary.E0);
        var b = etran.TrExpr(binary.E1);
        var intersection = QfSetIntersection(tok, a, b);
        Finite(a);
        Finite(b);
        Finite(intersection);
        if (binary.ResolvedOp is BinaryExpr.ResolvedOpcode.Union or BinaryExpr.ResolvedOpcode.Intersection) {
          Assume(Bpl.Expr.Eq(Bpl.Expr.Add(Card(QfSetUnion(tok, a, b)), Card(intersection)),
            Bpl.Expr.Add(Card(a), Card(b))));
        } else if (binary.ResolvedOp == BinaryExpr.ResolvedOpcode.SetDifference) {
          Assume(Bpl.Expr.Eq(Card(s), Bpl.Expr.Sub(Card(a), Card(intersection))));
        }
      }
    }
    if (expression is BinaryExpr comparison && comparison.E0.Type.NormalizeToAncestorType() is SetType { Finite: true } &&
        comparison.E1.Type.NormalizeToAncestorType() is SetType { Finite: true } &&
        comparison.ResolvedOp is BinaryExpr.ResolvedOpcode.Subset or BinaryExpr.ResolvedOpcode.ProperSubset) {
      var a = etran.TrExpr(comparison.E0);
      var b = etran.TrExpr(comparison.E1);
      Assume(BplImp(QfSetSubset(tok, a, b), Bpl.Expr.Le(Card(a), Card(b))));
      Assume(BplImp(BplAnd(QfSetSubset(tok, a, b), Bpl.Expr.Not(QfSetEqual(tok, a, b))), Bpl.Expr.Lt(Card(a), Card(b))));
    }
  }
}
