using System.Linq;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {
  private static Bpl.Expr QfWithoutTypeCoercion(Bpl.Expr expression) {
    while (expression is Bpl.NAryExpr { Fun: Bpl.TypeCoercion } coercion) {
      expression = coercion.Args[0];
    }
    return expression;
  }

  private void ConfigureQfNativeArrays() {
    if (!UseQuantifierFreeVerification) {
      return;
    }
    // Allocation and finite sets share their index sort. This avoids a lambda
    // converting a reference-indexed allocation map to a boxed set on every
    // frame comparison. Only boxed references are selected or updated.
    sink.TopLevelDeclarations.OfType<Bpl.GlobalVariable>().Single(v => v.Name == "$Alloc")
      .TypedIdent.Type = AllocMapType(Bpl.Token.NoToken);

    Bpl.Function Find(string name) => sink.Functions.Single(f => f.Name == name);
    void Builtin(Bpl.Function f, string builtin) {
      f.Body = null;
      f.Attributes = new Bpl.QKeyValue(f.tok, "builtin", [builtin], null);
    }
    Bpl.Function ArrayOperation(string name, string builtin, bool constant = false) {
      var f = new Bpl.Function(Bpl.Token.NoToken, name, [],
        [BplFormalVar("a", constant ? Bpl.Type.Bool : Predef.SetType, true)],
        BplFormalVar(null, Predef.SetType, false), null) { AlwaysRevealed = true };
      Builtin(f, builtin);
      sink.AddTopLevelDeclaration(f);
      return f;
    }
    var empty = Find("Set#Empty");
    empty.Body = new Bpl.NAryExpr(empty.tok, new Bpl.FunctionCall(ArrayOperation("$QfSetConst", "MapConst", true)), [Bpl.Expr.False]);
    Builtin(Find("Set#Union"), "MapOr");
    Builtin(Find("Set#Intersection"), "MapAnd");
    var not = ArrayOperation("$QfSetNot", "MapNot");
    var difference = Find("Set#Difference");
    var a = new Bpl.IdentifierExpr(difference.tok, difference.InParams[0]);
    var b = new Bpl.IdentifierExpr(difference.tok, difference.InParams[1]);
    difference.Body = new Bpl.NAryExpr(difference.tok, new Bpl.FunctionCall(Find("Set#Intersection")),
      [a, new Bpl.NAryExpr(difference.tok, new Bpl.FunctionCall(not), [b])]);
    foreach (var name in new[] { "Set#Subset", "Set#Disjoint" }) {
      var f = Find(name);
      var left = new Bpl.IdentifierExpr(f.tok, f.InParams[0]);
      var right = new Bpl.IdentifierExpr(f.tok, f.InParams[1]);
      var tok = ToDafnyToken(f.tok);
      f.Body = name == "Set#Subset" ? QfSetSubset(tok, left, right) : QfSetDisjoint(tok, left, right);
      f.Attributes = InlineAttribute(f.tok, f.Attributes);
    }
  }
}
