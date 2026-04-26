using System;
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
      ITEExpr iteExpr =>
        $"If({GetSupportShapeKey(definition, iteExpr.Test)},{GetSupportShapeKey(definition, iteExpr.Thn)},{GetSupportShapeKey(definition, iteExpr.Els)})",
      UnaryOpExpr { ResolvedOp: UnaryOpExpr.ResolvedOpcode.BoolNot } unary => GetSupportShapeKey(definition, unary.E),
      BinaryExpr binaryExpr =>
        $"Union({GetSupportShapeKey(definition, binaryExpr.E0)},{GetSupportShapeKey(definition, binaryExpr.E1)})",
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

  List<Field> GetSupportSnapshotFields(Function function) {
    Contract.Requires(function != null);
    if (supportSnapshotFields.TryGetValue(function, out var existingFields)) {
      return existingFields;
    }

    if (function.Body?.Resolved is not { } body || !NeedsSupportFunction(function, body)) {
      existingFields = [];
    } else {
      var fields = new HashSet<Field>();
      CollectSupportSnapshotFields(function, body, fields);
      existingFields = fields.OrderBy(field => field.FullSanitizedName).ToList();
    }

    supportSnapshotFields[function] = existingFields;
    return existingFields;
  }

  void CollectSupportSnapshotFields(Function definition, Expression expr, HashSet<Field> fields) {
    expr = Expression.StripParens(expr).Resolved;
    switch (expr) {
      case LiteralExpr:
      case ThisExpr:
      case IdentifierExpr:
      case NameSegment:
      case BoogieWrapper:
        return;
      case MemberSelectExpr memberSelectExpr:
        CollectSupportSnapshotFields(definition, memberSelectExpr.Obj, fields);
        CollectValueSnapshotFields(memberSelectExpr.Obj, fields);
        return;
      case FunctionCallExpr functionCallExpr:
        CollectSupportSnapshotFields(definition, functionCallExpr.Receiver, fields);
        CollectValueSnapshotFields(functionCallExpr.Receiver, fields);
        foreach (var arg in functionCallExpr.Args) {
          CollectSupportSnapshotFields(definition, arg, fields);
          CollectValueSnapshotFields(arg, fields);
        }

        if (NeedsSupportFunction(functionCallExpr.Function, functionCallExpr.Function.Body?.Resolved)) {
          foreach (var supportField in GetSupportSnapshotFields(functionCallExpr.Function)) {
            fields.Add(supportField);
          }
        }

        return;
      case ITEExpr iteExpr:
        CollectSupportSnapshotFields(definition, iteExpr.Test, fields);
        CollectSupportSnapshotFields(definition, iteExpr.Thn, fields);
        CollectSupportSnapshotFields(definition, iteExpr.Els, fields);
        CollectValueSnapshotFields(iteExpr.Test, fields);
        return;
      case UnaryOpExpr { ResolvedOp: UnaryOpExpr.ResolvedOpcode.BoolNot } unary:
        CollectSupportSnapshotFields(definition, unary.E, fields);
        return;
      case BinaryExpr binaryExpr:
        CollectSupportSnapshotFields(definition, binaryExpr.E0, fields);
        CollectSupportSnapshotFields(definition, binaryExpr.E1, fields);
        if (TryGetNullGuardedDereferenceCondition(binaryExpr.E0, binaryExpr.E1, out _)) {
          CollectValueSnapshotFields(binaryExpr.E0, fields);
        }

        return;
      default:
        foreach (var subExpression in expr.SubExpressions) {
          CollectSupportSnapshotFields(definition, subExpression, fields);
        }

        return;
    }
  }

  void CollectValueSnapshotFields(Expression expr, HashSet<Field> fields) {
    expr = Expression.StripParens(expr).Resolved;
    switch (expr) {
      case LiteralExpr:
      case ThisExpr:
      case IdentifierExpr:
      case NameSegment:
      case BoogieWrapper:
        return;
      case MemberSelectExpr memberSelectExpr:
        CollectValueSnapshotFields(memberSelectExpr.Obj, fields);
        if (memberSelectExpr.Member is Field { IsMutable: true } field) {
          fields.Add(field);
        }

        return;
      case FunctionCallExpr functionCallExpr:
        CollectValueSnapshotFields(functionCallExpr.Receiver, fields);
        foreach (var arg in functionCallExpr.Args) {
          CollectValueSnapshotFields(arg, fields);
        }

        if (NeedsSupportFunction(functionCallExpr.Function, functionCallExpr.Function.Body?.Resolved)) {
          foreach (var supportField in GetSupportSnapshotFields(functionCallExpr.Function)) {
            fields.Add(supportField);
          }
        }

        return;
      default:
        foreach (var subExpression in expr.SubExpressions) {
          CollectValueSnapshotFields(subExpression, fields);
        }

        return;
    }
  }

  Bpl.Expr TranslateSupportExpr(Function definition, Expression expr, ExpressionTranslator etran,
    Bpl.Expr layerArgument, Bpl.Expr revealArgument) {
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
      MemberSelectExpr memberSelectExpr => TranslateMemberSupportExpr(definition, memberSelectExpr, etran,
        layerArgument, revealArgument),
      FunctionCallExpr functionCallExpr => TranslateFunctionCallSupportExpr(definition, functionCallExpr, etran,
        layerArgument, revealArgument),
      ITEExpr iteExpr => TranslateIteSupportExpr(definition, iteExpr, etran, layerArgument, revealArgument),
      UnaryOpExpr { ResolvedOp: UnaryOpExpr.ResolvedOpcode.BoolNot } unary => TranslateSupportExpr(definition, unary.E,
        etran, layerArgument, revealArgument),
      BinaryExpr binaryExpr => TranslateBinarySupportExpr(definition, binaryExpr, etran, layerArgument, revealArgument),
      _ => UnionSupports(expr.Origin, expr.SubExpressions.Select(subExpr =>
        TranslateSupportExpr(definition, subExpr, etran, layerArgument, revealArgument)))
    };
  }

  Bpl.Expr TranslateMemberSupportExpr(Function definition, MemberSelectExpr expr, ExpressionTranslator etran,
    Bpl.Expr layerArgument, Bpl.Expr revealArgument) {
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

  Bpl.Expr TranslateFunctionCallSupportExpr(Function definition, FunctionCallExpr expr, ExpressionTranslator etran,
    Bpl.Expr layerArgument, Bpl.Expr revealArgument) {
    Contract.Requires(definition != null);
    Contract.Requires(expr != null);
    Contract.Requires(etran != null);

    var argumentSupports = new List<Bpl.Expr> {
      TranslateSupportExpr(definition, expr.Receiver, etran, layerArgument, revealArgument)
    };
    argumentSupports.AddRange(expr.Args.Select(arg =>
      TranslateSupportExpr(definition, arg, etran, layerArgument, revealArgument)));

    var result = UnionSupports(expr.Origin, argumentSupports);
    if (!NeedsSupportFunction(expr.Function, expr.Function.Body?.Resolved)) {
      return result;
    }

    var supportFunction = GetCanonicalSupportFunction(expr.Function) ?? GetOrCreateSupportFunction(expr.Function);
    var supportArguments = etran.SupportFunctionInvocationArguments(expr, layerArgument, revealArgument);
    var callSupport = ApplySupportFunction(expr.Origin, supportFunction, supportArguments);
    return UnionSupports(expr.Origin, callSupport, result);
  }

  static bool IsNullLiteral(Expression expr) {
    expr = Expression.StripParens(expr).Resolved;
    return expr is LiteralExpr { Value: null };
  }

  static bool SameSupportRoot(Expression left, Expression right) {
    left = Expression.StripParens(left).Resolved;
    right = Expression.StripParens(right).Resolved;

    if (left is ThisExpr && right is ThisExpr) {
      return true;
    }

    if (left is IdentifierExpr leftId && right is IdentifierExpr rightId) {
      return leftId.Var == rightId.Var;
    }

    if (left is BoogieWrapper leftBoogie && right is BoogieWrapper rightBoogie) {
      return leftBoogie.Expr == rightBoogie.Expr;
    }

    if (left is MemberSelectExpr leftMember && right is MemberSelectExpr rightMember) {
      return leftMember.Member == rightMember.Member && SameSupportRoot(leftMember.Obj, rightMember.Obj);
    }

    return false;
  }

  static bool StartsWithSupportRoot(Expression expr, Expression root) {
    expr = Expression.StripParens(expr).Resolved;
    return SameSupportRoot(expr, root) || expr switch {
      MemberSelectExpr memberSelectExpr => StartsWithSupportRoot(memberSelectExpr.Obj, root),
      FunctionCallExpr functionCallExpr => StartsWithSupportRoot(functionCallExpr.Receiver, root),
      SeqSelectExpr seqSelectExpr => StartsWithSupportRoot(seqSelectExpr.Seq, root),
      MultiSelectExpr multiSelectExpr => StartsWithSupportRoot(multiSelectExpr.Array, root),
      _ => false
    };
  }

  static bool MightDereferenceRoot(Expression expr, Expression root) {
    expr = Expression.StripParens(expr).Resolved;
    if (expr switch {
          MemberSelectExpr memberSelectExpr => StartsWithSupportRoot(memberSelectExpr.Obj, root),
          FunctionCallExpr functionCallExpr => StartsWithSupportRoot(functionCallExpr.Receiver, root),
          SeqSelectExpr seqSelectExpr => StartsWithSupportRoot(seqSelectExpr.Seq, root),
          MultiSelectExpr multiSelectExpr => StartsWithSupportRoot(multiSelectExpr.Array, root),
          _ => false
        }) {
      return true;
    }

    return expr.SubExpressions.Any(subExpr => MightDereferenceRoot(subExpr, root));
  }

  static bool TryGetNullGuardedDereferenceCondition(Expression guard, Expression rhs,
    out bool evaluatesRightWhenGuardTrue) {
    evaluatesRightWhenGuardTrue = false;

    guard = Expression.StripParens(guard).Resolved;

    if (guard is not BinaryExpr {
          ResolvedOp: BinaryExpr.ResolvedOpcode.EqCommon
          or BinaryExpr.ResolvedOpcode.NeqCommon
        } binaryExpr) {
      
      return false;
    }

    Expression root;
    if (IsNullLiteral(binaryExpr.E0)) {
      root = Expression.StripParens(binaryExpr.E1).Resolved;
    } else if (IsNullLiteral(binaryExpr.E1)) {
      root = Expression.StripParens(binaryExpr.E0).Resolved;
    } else {
      return false;
    }

    if (!MightDereferenceRoot(rhs, root)) {
      return false;
    }

    evaluatesRightWhenGuardTrue = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.NeqCommon;
    return true;
  }

  Bpl.Expr TranslateBinarySupportExpr(Function definition, BinaryExpr expr, ExpressionTranslator etran,
    Bpl.Expr layerArgument, Bpl.Expr revealArgument) {
    Contract.Requires(definition != null);
    Contract.Requires(expr != null);
    Contract.Requires(etran != null);

    var left = TranslateSupportExpr(definition, expr.E0, etran, layerArgument, revealArgument);
    var right = TranslateSupportExpr(definition, expr.E1, etran, layerArgument, revealArgument);

    // hacky solution to handle short-circuit ite
    if (TryGetNullGuardedDereferenceCondition(expr.E0, expr.E1, out var evaluatesRightWhenGuardTrue)) {
      var guard = etran.TrExpr(expr.E0);
      return expr.ResolvedOp switch {
        // n != null && expr: right only evaluated when guard true
        BinaryExpr.ResolvedOpcode.And when evaluatesRightWhenGuardTrue =>
          UnionSupports(expr.Origin, left,
            ConditionalSupport(expr.Origin, guard, right, EmptySupport(expr.Origin))),
        // n == null || expr: right only evaluated when guard false  
        BinaryExpr.ResolvedOpcode.Or when !evaluatesRightWhenGuardTrue =>
          UnionSupports(expr.Origin, left,
            ConditionalSupport(expr.Origin, guard, EmptySupport(expr.Origin), right)),
        _ => UnionSupports(expr.Origin, left, right)
      };
    }

    return UnionSupports(expr.Origin, left, right);
  }

  Bpl.Expr TranslateIteSupportExpr(Function definition, ITEExpr expr, ExpressionTranslator etran,
    Bpl.Expr layerArgument, Bpl.Expr revealArgument) {
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
