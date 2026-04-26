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

  Bpl.Expr ConditionalSupport(IOrigin tok, Bpl.Expr guard, Bpl.Expr thenSupport, Bpl.Expr elseSupport) {
    return new Bpl.NAryExpr(tok, new Bpl.IfThenElse(tok),
      new List<Bpl.Expr> { guard, thenSupport, elseSupport }) {
      Type = Predef.SetType
    };
  }

  Bpl.Expr ApplySupportFunction(IOrigin tok, Bpl.Function supportFunction, List<Bpl.Expr> arguments) {
    return new Bpl.NAryExpr(tok, new Bpl.FunctionCall(supportFunction), arguments) {
      Type = Predef.SetType
    };
  }

  string GetSupportShapeKey(Function definition, Expression expr) {
    Contract.Requires(definition != null);
    Contract.Requires(expr != null);

    expr = expr.Resolved;
    return expr switch {
      LiteralExpr => "Empty",
      ThisExpr => "Empty",
      IdentifierExpr => "Empty",
      NameSegment => "Empty",
      BoogieWrapper => "Empty",
      MemberSelectExpr memberSelectExpr => GetMemberSupportShapeKey(definition, memberSelectExpr),
      FunctionCallExpr functionCallExpr => GetFunctionCallSupportShapeKey(definition, functionCallExpr),
      ITEExpr iteExpr => $"If({GetSupportShapeKey(definition, iteExpr.Test)},{GetSupportShapeKey(definition, iteExpr.Thn)},{GetSupportShapeKey(definition, iteExpr.Els)})",
      UnaryOpExpr { ResolvedOp: UnaryOpExpr.ResolvedOpcode.BoolNot } unary => GetSupportShapeKey(definition, unary.E),
      BinaryExpr binaryExpr => $"Union({GetSupportShapeKey(definition, binaryExpr.E0)},{GetSupportShapeKey(definition, binaryExpr.E1)})",
      _ => $"Union({string.Join(",", expr.SubExpressions.Select(subExpr => GetSupportShapeKey(definition, subExpr)))})"
    };
  }

  string GetMemberSupportShapeKey(Function definition, MemberSelectExpr expr) {
    var objectSupport = GetSupportShapeKey(definition, expr.Obj);
    if (expr.Member is not Field field || !field.IsMutable) {
      return objectSupport;
    }
    return $"Field({field.FullSanitizedName},{objectSupport})";
  }

  string GetFunctionCallSupportShapeKey(Function definition, FunctionCallExpr expr) {
    var argumentShapes = new List<string> {
      GetSupportShapeKey(definition, expr.Receiver)
    };
    argumentShapes.AddRange(expr.Args.Select(arg => GetSupportShapeKey(definition, arg)));
    var argumentsKey = string.Join(",", argumentShapes);
    if (!NeedsSupportFunction(expr.Function, expr.Function.Body?.Resolved)) {
      return $"Args({argumentsKey})";
    }

    var calleeKey = expr.Function == definition ? "Self" : expr.Function.FullSanitizedName;
    return $"Call({calleeKey};{argumentsKey})";
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

    var snapshotState = etran.ObjectFieldSnapshotState;
    var supportFunction = snapshotState is null || snapshotState.IsBaseState
      ? GetCanonicalSupportFunction(expr.Function) ?? GetOrCreateSupportFunction(expr.Function)
      : GetOrCreateSupportFunction(expr.Function, snapshotState);
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
      BinaryExpr.ResolvedOpcode.And => UnionSupports(expr.Origin, left,
        ConditionalSupport(expr.Origin, etran.TrExpr(expr.E0), right, EmptySupport(expr.Origin))),
      BinaryExpr.ResolvedOpcode.Or => UnionSupports(expr.Origin, left,
        ConditionalSupport(expr.Origin, etran.TrExpr(expr.E0), EmptySupport(expr.Origin), right)),
      BinaryExpr.ResolvedOpcode.Imp => UnionSupports(expr.Origin, left,
        ConditionalSupport(expr.Origin, etran.TrExpr(expr.E0), right, EmptySupport(expr.Origin))),
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
    var branchSupport = ConditionalSupport(expr.Origin, guard, thenSupport, elseSupport);
    return UnionSupports(expr.Origin, guardSupport, branchSupport);
  }
}
