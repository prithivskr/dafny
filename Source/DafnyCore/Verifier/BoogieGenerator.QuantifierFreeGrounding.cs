using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {
  private void LowerQuantifierFreeProgram() {
    if (!options.UseArrayTheory) {
      reporter.Error(MessageSource.Verifier, forModule.Origin,
        "Quantifier-free verification requires native SMT arrays; /useArrayAxioms is incompatible with --qf-heap --p3.");
      sink = new Bpl.Program();
      return;
    }
    // Ground the typed program: otherwise polymorphic boxing/map operations
    // would introduce new quantified type axioms after this pass.
    if (sink.Resolve(options) != 0 || sink.Typecheck(options) != 0) {
      throw new InvalidOperationException("QF lowering requires a well-typed Boogie program");
    }
    var status = Bpl.Monomorphizer.Monomorphize(options, sink);
    if (!Bpl.MonomorphismChecker.IsMonomorphic(sink)) {
      reporter.Error(MessageSource.Verifier, forModule.Origin,
        $"Quantifier-free verification could not specialize the Boogie program ({status}).");
      sink = new Bpl.Program();
      return;
    }
    new QfGrounder(sink).Run();
    var audit = new QfGrounder.QfTerms();
    audit.Visit(sink);
    foreach (var axiom in QfAxioms(sink)) {
      audit.VisitExpr(axiom.Expr);
    }
    if (audit.FirstBinder != null) {
      reporter.Error(MessageSource.Verifier, ToDafnyToken(audit.FirstBinder.tok),
        "Quantifier-free verification does not support this quantified expression or map comprehension.");
      sink = new Bpl.Program();
    }
  }

  private static IEnumerable<Bpl.Axiom> QfAxioms(Bpl.Program program) =>
    program.TopLevelDeclarations.OfType<Bpl.Axiom>()
      .Concat(program.Functions.SelectMany(function => function.OtherDefinitionAxioms))
      .Concat(program.Functions.Select(function => function.DefinitionAxiom).Where(axiom => axiom != null))
      .Concat(program.TopLevelDeclarations.OfType<Bpl.Constant>().SelectMany(constant => constant.DefinitionAxioms))
      .Distinct();

  private sealed class QfGrounder {
    private readonly Bpl.Program program;
    private readonly Dictionary<string, List<(Bpl.ForallExpr Axiom, Bpl.Expr Pattern)>> templates = new();
    private bool unfoldOpaque;
    private Dictionary<string, Bpl.Function> functions;
    private Bpl.Constant zeroLayer;

    public QfGrounder(Bpl.Program program) { this.program = program; }

    private static string Head(Bpl.Expr e) => e is Bpl.NAryExpr { Fun: Bpl.FunctionCall call }
      ? call.FunctionName : null;

    public void Run() {
      functions = program.Functions.ToDictionary(f => f.Name);
      zeroLayer = program.TopLevelDeclarations.OfType<Bpl.Constant>().Single(c => c.Name == "$LZ");
      // Definition axioms can live only in a declaration's `uses` list after
      // monomorphization. Include those as well as top-level axioms; otherwise
      // the printed Boogie program retains quantified identity definitions.
      foreach (var axiom in QfAxioms(program).ToList()) {
        if (axiom.Expr is not Bpl.ForallExpr q) {
          continue;
        }
        program.RemoveTopLevelDeclaration(axiom);
        foreach (var function in program.Functions) {
          function.OtherDefinitionAxioms.Remove(axiom);
          if (function.DefinitionAxiom == axiom) { function.DefinitionAxiom = null; }
        }
        foreach (var constant in program.TopLevelDeclarations.OfType<Bpl.Constant>()) { constant.DefinitionAxioms.Remove(axiom); }
        // Nested quantified background properties are not ground templates.
        // Omitting an axiom weakens the proof context; it never proves a goal.
        if (QfTerms.HasBinder(q.Body)) { continue; }
        for (var trigger = q.Triggers; trigger != null; trigger = trigger.Next) {
          foreach (var pattern in trigger.Tr) {
            var head = Head(pattern);
            if (head == null) { continue; }
            if (!templates.TryGetValue(head, out var list)) { templates[head] = list = []; }
            list.Add((q, pattern));
          }
        }
      }
      // Field identities and type constructors occur in ground declarations,
      // not necessarily in commands. Their inverse/tag instances establish,
      // for example, that writing `next` cannot change the `data` field.
      foreach (var declaration in program.TopLevelDeclarations.OfType<Bpl.Axiom>().ToList()) {
        var facts = new Bpl.Axiom(declaration.tok, Facts(declaration.Expr));
        facts.Attributes = new Bpl.QKeyValue(declaration.tok, "include_dep", [], null);
        program.AddTopLevelDeclaration(facts);
      }
      var variables = program.TopLevelDeclarations.OfType<Bpl.GlobalVariable>().Cast<Bpl.Variable>()
        .Concat(program.Procedures.SelectMany(p => p.InParams.Concat(p.OutParams)))
        .Concat(program.Implementations.SelectMany(i => i.InParams.Concat(i.OutParams).Concat(i.LocVars)));
      foreach (var variable in variables.Distinct()) {
        if (variable.TypedIdent.WhereExpr is { } where) {
          variable.TypedIdent.WhereExpr = Bpl.Expr.And(Facts(where), where);
        }
      }
      foreach (var proc in program.Procedures.ToList()) {
        var extraRequires = proc.Requires.Select(r => new Bpl.Requires(r.tok, true, Facts(r.Condition), null)).ToList();
        var extraEnsures = proc.Ensures.Select(e => new Bpl.Ensures(e.tok, true, Facts(e.Condition), null)).ToList();
        proc.Requires.AddRange(extraRequires);
        proc.Ensures.AddRange(extraEnsures);
      }
      foreach (var impl in program.Implementations) {
        unfoldOpaque = impl.Blocks.SelectMany(b => b.Cmds).OfType<Bpl.CallCmd>()
          .Any(c => c.Proc.Ensures.Any(e => e.Condition is Bpl.IdentifierExpr id &&
            id.Name.StartsWith("reveal_", StringComparison.Ordinal)));
        impl.StructuredStmts = null;
        var formalMap = impl.Proc.InParams.Concat(impl.Proc.OutParams)
          .Zip(impl.InParams.Concat(impl.OutParams)).ToDictionary(p => p.First,
            p => (Bpl.Expr)new Bpl.IdentifierExpr(p.Second.tok, p.Second));
        var postFacts = Facts(impl.Proc.Ensures.Where(e => !e.Free).Select(e =>
          Bpl.Substituter.Apply(v => formalMap.GetValueOrDefault(v), e.Condition)));
        foreach (var block in impl.Blocks) {
          var cmds = new List<Bpl.Cmd>();
          var grounded = new HashSet<string>();
          foreach (var cmd in block.Cmds) {
            var terms = new QfTerms();
            terms.Visit(cmd);
            if (cmd is Bpl.CallCmd call) {
              var inputs = call.Proc.InParams.Zip(call.Ins).ToDictionary(p => p.First, p => p.Second);
              foreach (var require in call.Proc.Requires.Where(r => !r.Free)) {
                terms.VisitExpr(Bpl.Substituter.Apply(v => inputs.GetValueOrDefault(v), require.Condition));
              }
            }
            var facts = Facts(terms.Expressions, grounded);
            if (facts != Bpl.Expr.True) { cmds.Add(new Bpl.AssumeCmd(cmd.tok, facts)); }
            cmds.Add(cmd);
            if (cmd is Bpl.AssignCmd or Bpl.HavocCmd or Bpl.CallCmd) { grounded.Clear(); }
          }
          if (block.TransferCmd is Bpl.ReturnCmd) {
            cmds.Add(new Bpl.AssumeCmd(block.tok, postFacts));
          }
          if (block.TransferCmd is Bpl.GotoCmd jump) {
            // Boogie moves loop-head assertions to incoming edges when it
            // cuts loops. Supply their instances in the incoming state too;
            // a free invariant at the head alone does not help preservation.
            var edgeFacts = Facts(jump.LabelTargets.SelectMany(target => target.Cmds
              .TakeWhile(command => command is Bpl.PredicateCmd).OfType<Bpl.AssertCmd>())
              .Select(assertion => assertion.Expr));
            cmds.Add(new Bpl.AssumeCmd(block.tok, edgeFacts));
          }
          block.Cmds = cmds;
        }
      }
    }

    private Bpl.Expr Facts(Bpl.Expr expression) => Facts([expression]);

    private Bpl.Expr Facts(IEnumerable<Bpl.Expr> expressions, HashSet<string> grounded = null) {
      var queue = new Queue<(Bpl.Expr Term, ImmutableHashSet<Bpl.ForallExpr> Expanded)>();
      var seen = grounded ?? new HashSet<string>();
      var instances = new Dictionary<string, Bpl.Expr>();
      void Add(Bpl.Expr expression, ImmutableHashSet<Bpl.ForallExpr> expanded) {
        var terms = new QfTerms();
        terms.VisitExpr(expression);
        foreach (var term in terms.Expressions) {
          if (seen.Add(term.ToString())) { queue.Enqueue((term, expanded)); }
        }
      }
      foreach (var expression in expressions) { Add(expression, ImmutableHashSet<Bpl.ForallExpr>.Empty); }
      while (queue.TryDequeue(out var item)) {
        if (Head(item.Term) is not { } head) { continue; }
        if (item.Term is Bpl.NAryExpr { Fun: Bpl.FunctionCall functionCall } call && !head.EndsWith("#requires")) {
          var name = head.EndsWith("#canCall") ? head[..^8] : head;
          if (functions.TryGetValue(name + "#requires", out var requires)) {
            var args = call.Args.Where((_, i) => functionCall.Func.InParams[i].Name != "$reveal").ToList();
            if (requires.InParams.Count == args.Count + 1 && requires.InParams[0].TypedIdent.Type.Equals(zeroLayer.TypedIdent.Type)) {
              args.Insert(0, new Bpl.IdentifierExpr(call.tok, zeroLayer));
            }
            if (requires.InParams.Count == args.Count && requires.InParams.Zip(args).All(p => p.First.TypedIdent.Type.Equals(p.Second.Type ?? p.Second.ShallowType))) {
              Add(new Bpl.NAryExpr(call.tok, new Bpl.FunctionCall(requires), args), item.Expanded);
            }
          }
        }
        if (!templates.TryGetValue(head, out var rules)) { continue; }
        foreach (var (axiom, pattern) in rules) {
          if (!unfoldOpaque && pattern is Bpl.NAryExpr application &&
              application.Args.Any(a => a is Bpl.LiteralExpr { isBool: true })) { continue; }
          var bindings = new Dictionary<Bpl.Variable, Bpl.Expr>();
          if (!Match(pattern, item.Term, bindings) || axiom.Dummies.Any(v => !bindings.ContainsKey(v))) { continue; }
          var instance = Bpl.Substituter.Apply(v => bindings.GetValueOrDefault(v), axiom.Body);
          // Follow acyclic definition dependencies to arbitrary depth. Stop
          // term discovery when an axiom repeats on this path, so recursive
          // definitions and inverse axioms cannot grow an infinite worklist.
          // The closing instance itself is still a valid ground fact.
          if (instances.TryAdd(instance.ToString(), instance) && !item.Expanded.Contains(axiom) &&
              !head.StartsWith("$Box") && !head.StartsWith("$Unbox")) {
            Add(instance, item.Expanded.Add(axiom));
          }
        }
      }
      return instances.Values.Aggregate((Bpl.Expr)Bpl.Expr.True, Bpl.Expr.And);
    }

    private static bool Match(Bpl.Expr pattern, Bpl.Expr term, Dictionary<Bpl.Variable, Bpl.Expr> bindings) {
      if (pattern is Bpl.IdentifierExpr { Decl: Bpl.BoundVariable variable }) {
        if (!variable.TypedIdent.Type.Equals(term.Type ?? term.ShallowType)) { return false; }
        if (!bindings.ContainsKey(variable)) { bindings[variable] = term; }
        return true;
      }
      if (pattern is Bpl.NAryExpr p && term is Bpl.NAryExpr t && p.Fun.FunctionName == t.Fun.FunctionName && p.Args.Count == t.Args.Count) {
        return p.Args.Zip(t.Args).All(pair => Match(pair.First, pair.Second, bindings));
      }
      // Constants in a pattern need not be syntactically equal to the observed
      // term. The instance retains the original constant, so SMT can connect
      // them only if the proof context actually establishes equality.
      return pattern is Bpl.LiteralExpr { isBool: true } || pattern.ToString() == term.ToString();
    }

    public sealed class QfTerms : Bpl.ReadOnlyVisitor {
      public readonly List<Bpl.Expr> Expressions = [];
      private bool binder;
      public Bpl.BinderExpr FirstBinder { get; private set; }
      public static bool HasBinder(Bpl.Expr e) { var v = new QfTerms(); v.VisitExpr(e); return v.binder; }
      public override Bpl.Expr VisitNAryExpr(Bpl.NAryExpr node) {
        Expressions.Add(node);
        return base.VisitNAryExpr(node);
      }
      public override Bpl.BinderExpr VisitBinderExpr(Bpl.BinderExpr node) {
        binder = true;
        FirstBinder ??= node;
        return node;
      }
    }
  }
}
