using System.Linq;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {
  private void ConfigureP3SetEquality() {
    if (!options.Get(CommonOptionBag.Prelude3) || options.DafnyPrelude != null ||
        (options.TypeEncodingMethod == Bpl.CoreOptions.TypeEncoding.Monomorphic && options.UseArrayTheory)) {
      return;
    }

    // The p3 prelude represents sets by maps and implements Set#Equal as map
    // equality. Boogie's erased-map encoding supplies select/store axioms, but
    // not extensionality: even S + {} == S otherwise fails. Keep equality as a
    // named term so it can trigger extensionality for the compared sets only.
    var equal = sink.TopLevelDeclarations.OfType<Bpl.Function>().Single(f => f.Name == "Set#Equal");
    equal.Body = null;
    equal.Attributes = RemoveInline(equal.Attributes);

    var tok = equal.tok;
    var aVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$a", Predef.SetType));
    var bVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$b", Predef.SetType));
    var a = new Bpl.IdentifierExpr(tok, aVar);
    var b = new Bpl.IdentifierExpr(tok, bVar);
    var equalCall = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(equal), [a, b]);
    sink.AddTopLevelDeclaration(new Bpl.Axiom(tok,
      new Bpl.ForallExpr(tok, [aVar, bVar], BplTrigger(equalCall), Bpl.Expr.Iff(equalCall, Bpl.Expr.Eq(a, b))),
      "p3 set equality"));

    // Skolemized extensionality: different sets differ at some element. This
    // avoids a nested forall over elements for every equality comparison.
    var witness = new Bpl.Function(tok, "$P3SetDifferenceWitness", [],
      [BplFormalVar("a", Predef.SetType, true), BplFormalVar("b", Predef.SetType, true)],
      BplFormalVar(null, Predef.BoxType, false), null) { AlwaysRevealed = true };
    sink.AddTopLevelDeclaration(witness);
    var element = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(witness), [a, b]);
    sink.AddTopLevelDeclaration(new Bpl.Axiom(tok,
      new Bpl.ForallExpr(tok, [aVar, bVar], BplTrigger(equalCall),
        Bpl.Expr.Or(equalCall, Bpl.Expr.Neq(Bpl.Expr.Select(a, element), Bpl.Expr.Select(b, element)))),
      "p3 set extensionality"));

    // Subset/disjointness are background array operations. Express them using
    // difference/intersection and extensional equality, avoiding the prelude's
    // nested element quantifiers at every frame-rule instantiation.
    foreach (var name in new[] { "Set#Subset", "Set#Disjoint" }) {
      foreach (var axiom in sink.TopLevelDeclarations.OfType<Bpl.Axiom>().Where(axiom =>
                 axiom.Expr is Bpl.ForallExpr { Body: Bpl.NAryExpr binary } && binary.Args.Count == 2 &&
                 binary.Args[0] is Bpl.NAryExpr { Fun: Bpl.FunctionCall call } && call.FunctionName == name).ToList()) {
        sink.RemoveTopLevelDeclaration(axiom);
      }
      var function = sink.TopLevelDeclarations.OfType<Bpl.Function>().Single(f => f.Name == name);
      var left = new Bpl.IdentifierExpr(tok, function.InParams[0]);
      var right = new Bpl.IdentifierExpr(tok, function.InParams[1]);
      var origin = ToDafnyToken(tok);
      function.Body = name == "Set#Subset" ? QfSetSubset(origin, left, right) : QfSetDisjoint(origin, left, right);
      function.Attributes = InlineAttribute(tok, function.Attributes);
    }

    static Bpl.QKeyValue RemoveInline(Bpl.QKeyValue attributes) {
      if (attributes == null) {
        return null;
      }
      if (attributes.Key == "inline") {
        return RemoveInline(attributes.Next);
      }
      attributes.Next = RemoveInline(attributes.Next);
      return attributes;
    }
  }
}
