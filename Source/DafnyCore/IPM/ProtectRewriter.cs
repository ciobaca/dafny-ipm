#nullable enable
using Microsoft.Dafny;
using static Microsoft.Boogie.CollectionExtensions;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;
using static Microsoft.Dafny.Util;

namespace DafnyCore.IPM;
public class ProtectRewriter(ErrorReporter r) : IRewriter(r) { // TODO: Figure out if the class can Extend Rewriter instead of IRewriter
  // TODOs:
  //  - figure out where you can call (some SystemModuleManager).CreateArrowTypeDecl(2) directly or deferred

  internal override void PreResolve(Program program) {
    //var moduleDefinition = new ModuleDefinition(
    //  SourceOrigin.NoToken,
    //  new Name("_ITP"),
    //  [],
    //  ModuleKindEnum.Concrete,
    //  null,
    //  program.DefaultModuleDef,
    //  null,
    //  []
    //);
    //var sig = new ModuleSignature() {
    //  ModuleDef = moduleDefinition,
    //  IsAbstract = moduleDefinition.ModuleKind == ModuleKindEnum.Abstract,
    //  VisibilityScope = new()
    //};
    //sig.VisibilityScope.Augment(moduleDefinition.VisibilityScope);
    //Contract.Assert(moduleDefinition.DefaultClass is not null);
    //moduleDefinition.DefaultClass.Members.AddRange(ProtectorFunctions);
    //moduleDefinition.DefaultClass.SetMembersBeforeResolution();
    //program.DefaultModuleDef.SourceDecls.Add(new LiteralModuleDecl(Options, moduleDefinition, program.DefaultModuleDef, Guid.NewGuid()));
    //  program.SystemModuleManager.CreateArrowTypeDecl(2);// this doesn't work for some reason, prolly bcs it's done after parsing :(
  }

  private static IEnumerable<Statement> statementsOf(Expression e) => e switch {
    StmtExpr se => Concat(statementsOf(se.S), statementsOf(se.E)),
    ConcreteSyntaxExpression cse => cse.PreResolveSubExpressions.SelectMany(statementsOf),
    DatatypeValue dv => dv.Bindings.ArgumentBindings.SelectMany(ab => statementsOf(ab.Actual)),
    _ => e.SubExpressions.SelectMany(statementsOf),
  };
  private static IEnumerable<Expression> expressionsOf(Expression e) => Concat([e], e switch {
    StmtExpr se => Concat(expressionsOf(se.S), expressionsOf(se.E)),
    ConcreteSyntaxExpression cse => cse.PreResolveSubExpressions.SelectMany(expressionsOf),
    DatatypeValue dv => dv.Bindings.ArgumentBindings.SelectMany(ab => expressionsOf(ab.Actual)),
    _ => e.SubExpressions.SelectMany(expressionsOf),
  });

  // curious things happen in `AssignOrReturnStmt` and you will NOT catch me asking questions;
  // for example, issues regarding `PreResolveSubEXpressions` and, in particular, the part
  // originating from `Rhss` will be handled as they appear
  private static IEnumerable<Statement> statementsOf(Statement s) =>
    Concat([s], s.PreResolveSubStatements.SelectMany(statementsOf), s.PreResolveSubExpressions.SelectMany(statementsOf)
  );
  private static IEnumerable<Expression> expressionsOf(Statement s) =>
    Concat(s.PreResolveSubStatements.SelectMany(expressionsOf), s.PreResolveSubExpressions.SelectMany(expressionsOf));
  internal override void PreResolve(ModuleDefinition moduleDefinition) {
    Contract.Requires(moduleDefinition.DefaultClass is not null);
    Contract.Requires(moduleDefinition.TopLevelDecls.OfType<AbstractModuleDecl>().None());
    Contract.Requires(moduleDefinition.TopLevelDecls.None(d => d is TypeParameter or AmbiguousTopLevelDecl
                                                                 or InternalTypeSynonymDecl or NonNullTypeDecl));

    static void ReplaceExpressionInAssertStatement(AssertStmt a) {
      if (Attributes.Contains(a.Attributes, "ipm")) {
        //Console.WriteLine("Protecting to prove assertion " + a.Expr.ToString());
        a.Expr = ProtectToProveFunction.CallOn(a.Expr);
      } else {
        a.Expr = ExprReplacer.ReplaceExpr(a.Expr);
        //Console.WriteLine($"assert statement: {a.Expr}");
      }
    }
    foreach (var d in moduleDefinition.TopLevelDecls.Where(d => d is not ModuleDecl)) { switch (d) {
      case TopLevelDeclWithMembers decl:
        foreach (var member in decl.Members.OfType<MethodOrFunction>()) {
          foreach (var req in member.Req) {
            req.E = ExprReplacer.ReplaceExpr(req.E);
            //Console.WriteLine($"requires clause: {req.E}");
          }
          foreach (var ens in member.Ens) {
            if (Attributes.Contains(ens.Attributes, "ipm")) {
              //Console.WriteLine("Protecting to prove ensures clause " + ens.E.ToString());
              ens.E = ProtectToProveFunction.CallOn(ens.E);
            } else {
              ens.E = ExprReplacer.ReplaceExpr(ens.E);
            }
            //Console.WriteLine($"ensures clause: {ens.E}");
          }
          switch (member) {
            case Function { Body: { } } f:
              statementsOf(f.Body).OfType<AssertStmt>().ForEach(ReplaceExpressionInAssertStatement);
              //expressionsOf(f.Body).OfType<ApplySuffix>().ForEach(null);
              break;
            case MethodOrConstructor { Body: { } } mc:
              mc.Body.Body.SelectMany(statementsOf).OfType<AssertStmt>().ForEach(ReplaceExpressionInAssertStatement);
              //mc.Body.Body.SelectMany(expressionsOf).OfType<ApplySuffix>().ForEach(null);
              break;
            default:
              throw new UnreachableException();
          }
        }
        break;
      case SubsetTypeDecl decl:
        statementsOf(decl.Constraint).OfType<AssertStmt>().ForEach(ReplaceExpressionInAssertStatement);
        if (decl.Witness is not null) {
          statementsOf(decl.Witness).OfType<AssertStmt>().ForEach(ReplaceExpressionInAssertStatement);
        }
        break;
      case ConcreteTypeSynonymDecl:
        break;
      default:
        throw new UnreachableException();
    } }

    var protectorFunctions = (
      new ProtectFunction(),
      new ProtectToProveFunction(),
      new ProtectScopeFunction()
    );
    moduleDefinition.DefaultClass!.Members = [.. protectorFunctions.ToEnumerable<Function>(), .. moduleDefinition.DefaultClass!.Members];
    moduleDefinition.InitProtectorFunctions(protectorFunctions);
  }
}
