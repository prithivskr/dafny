using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {
  Bpl.Expr EmptySupport(IOrigin tok) {
    return FunctionCall(tok, BuiltinFunction.SetEmpty, Predef.BoxType);
  }

  Bpl.Expr UnionSupports(IOrigin tok, Bpl.Expr left, Bpl.Expr right) {
    return FunctionCall(tok, BuiltinFunction.SetUnion, Predef.BoxType, left, right);
  }

  Bpl.Expr UnionSupports(IOrigin tok, IEnumerable<Bpl.Expr> supports) {
    var result = EmptySupport(tok);
    foreach (var support in supports) {
      result = UnionSupports(tok, result, support);
    }
    return result;
  }

  Bpl.Expr UnionOneSupport(IOrigin tok, Bpl.Expr support, Bpl.Expr element) {
    return FunctionCall(tok, BuiltinFunction.SetUnionOne, Predef.BoxType, support, element);
  }

  Bpl.Expr ApplySupportFunction(IOrigin tok, Bpl.Function supportFunction, List<Bpl.Expr> arguments) {
    return new Bpl.NAryExpr(tok, new Bpl.FunctionCall(supportFunction), arguments) {
      Type = Predef.SetType
    };
  }

  Bpl.Expr TranslateSupportExpr(Function definition, Expression expr, ExpressionTranslator etran, Bpl.Expr layerArgument, Bpl.Expr revealArgument) {
    Contract.Requires(definition != null);
    Contract.Requires(expr != null);
    Contract.Requires(etran != null);

    expr = expr.Resolved;
    return expr switch {
      LiteralExpr => EmptySupport(expr.Origin),
      ThisExpr => EmptySupport(expr.Origin),
      IdentifierExpr => EmptySupport(expr.Origin),
      NameSegment => EmptySupport(expr.Origin),
      BoogieWrapper => EmptySupport(expr.Origin),
      MemberSelectExpr memberSelectExpr => TranslateMemberSupportExpr(definition, memberSelectExpr, etran, layerArgument, revealArgument),
      FunctionCallExpr functionCallExpr => TranslateFunctionCallSupportExpr(definition, functionCallExpr, etran, layerArgument, revealArgument),
      ITEExpr iteExpr => TranslateIteSupportExpr(definition, iteExpr, etran, layerArgument, revealArgument),
      UnaryOpExpr { ResolvedOp: UnaryOpExpr.ResolvedOpcode.BoolNot } unary => TranslateSupportExpr(definition, unary.E, etran, layerArgument, revealArgument),
      BinaryExpr binaryExpr => TranslateBinarySupportExpr(definition, binaryExpr, etran, layerArgument, revealArgument),
      _ => UnionSupports(expr.Origin, expr.SubExpressions.Select(subExpr =>
        TranslateSupportExpr(definition, subExpr, etran, layerArgument, revealArgument)))
    };
  }

  Bpl.Expr TranslateMemberSupportExpr(Function definition, MemberSelectExpr expr, ExpressionTranslator etran, Bpl.Expr layerArgument, Bpl.Expr revealArgument) {
    Contract.Requires(definition != null);
    Contract.Requires(expr != null);
    Contract.Requires(etran != null);

    var objectSupport = TranslateSupportExpr(definition, expr.Obj, etran, layerArgument, revealArgument);
    if (expr.Member is not Field field || !field.IsMutable) {
      return objectSupport;
    }

    var receiver = etran.TrExpr(expr.Obj);
    return UnionOneSupport(expr.Origin, objectSupport, ApplyBox(expr.Origin, receiver));
  }

  Bpl.Expr TranslateFunctionCallSupportExpr(Function definition, FunctionCallExpr expr, ExpressionTranslator etran, Bpl.Expr layerArgument, Bpl.Expr revealArgument) {
    Contract.Requires(definition != null);
    Contract.Requires(expr != null);
    Contract.Requires(etran != null);

    var argumentSupports = new List<Bpl.Expr> {
      TranslateSupportExpr(definition, expr.Receiver, etran, layerArgument, revealArgument)
    };
    argumentSupports.AddRange(expr.Args.Select(arg => TranslateSupportExpr(definition, arg, etran, layerArgument, revealArgument)));

    var result = UnionSupports(expr.Origin, argumentSupports);
    if (!NeedsSupportFunction(expr.Function, expr.Function.Body?.Resolved)) {
      return result;
    }

    var supportFunction = GetOrCreateSupportFunction(expr.Function);
    var supportArguments = etran.FunctionInvocationArguments(expr, layerArgument, revealArgument);
    var callSupport = ApplySupportFunction(expr.Origin, supportFunction, supportArguments);
    return UnionSupports(expr.Origin, callSupport, result);
  }

  Bpl.Expr TranslateBinarySupportExpr(Function definition, BinaryExpr expr, ExpressionTranslator etran, Bpl.Expr layerArgument, Bpl.Expr revealArgument) {
    Contract.Requires(definition != null);
    Contract.Requires(expr != null);
    Contract.Requires(etran != null);

    var left = TranslateSupportExpr(definition, expr.E0, etran, layerArgument, revealArgument);
    var right = TranslateSupportExpr(definition, expr.E1, etran, layerArgument, revealArgument);
    return expr.ResolvedOp switch {
      BinaryExpr.ResolvedOpcode.And => UnionSupports(expr.Origin, left, right),
      BinaryExpr.ResolvedOpcode.Or => UnionSupports(expr.Origin, left, right),
      _ => UnionSupports(expr.Origin, left, right)
    };
  }

  Bpl.Expr TranslateIteSupportExpr(Function definition, ITEExpr expr, ExpressionTranslator etran, Bpl.Expr layerArgument, Bpl.Expr revealArgument) {
    Contract.Requires(definition != null);
    Contract.Requires(expr != null);
    Contract.Requires(etran != null);

    var guardSupport = TranslateSupportExpr(definition, expr.Test, etran, layerArgument, revealArgument);
    var thenSupport = TranslateSupportExpr(definition, expr.Thn, etran, layerArgument, revealArgument);
    var elseSupport = TranslateSupportExpr(definition, expr.Els, etran, layerArgument, revealArgument);
    var guard = etran.TrExpr(expr.Test);
    var branchSupport = new Bpl.NAryExpr(expr.Origin, new Bpl.IfThenElse(expr.Origin),
      new List<Bpl.Expr> { guard, thenSupport, elseSupport }) {
      Type = Predef.SetType
    };
    return UnionSupports(expr.Origin, guardSupport, branchSupport);
  }
}
