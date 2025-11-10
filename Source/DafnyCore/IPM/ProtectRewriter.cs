#nullable enable
using Microsoft.Dafny;
using static Microsoft.Boogie.CollectionExtensions;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;

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
  internal override void PreResolve(ModuleDefinition moduleDefinition) {
    Contract.Requires(moduleDefinition.DefaultClass is not null);
    Contract.Requires(moduleDefinition.TopLevelDecls.OfType<AbstractModuleDecl>().None());
    Contract.Requires(moduleDefinition.TopLevelDecls.None(d => d is TypeParameter or AmbiguousTopLevelDecl
                                                                 or InternalTypeSynonymDecl or NonNullTypeDecl));
    //moduleDefinition.SourceDecls.Add(new AliasModuleDecl(
    //  Options,
    //  new SourceOrigin(Token.NoToken, Token.NoToken)/*maybe this'll work?*/,
    //  new([new("_ITP")]),
    //  new("_ITP"),
    //  null,
    //  moduleDefinition,
    //  true,
    //  [],
    //  Guid.NewGuid()
    //));
    static IEnumerable<AssertStmt> assertStatementsOfExpression(Microsoft.Dafny.Expression e) {
      if (e is StmtExpr statementExpression) {
        foreach (var assertStatementFromStatementExpression in assertStatementsOfStatement(statementExpression.S)) {
          yield return assertStatementFromStatementExpression;
        }
      }
      foreach (var assertStatementFromSubExpressions in e.SubExpressions.SelectMany(assertStatementsOfExpression)) {
        yield return assertStatementFromSubExpressions;
      }
    }
    static IEnumerable<AssertStmt> assertStatementsOfStatement(Statement s) {
      if (s is AssertStmt assertStatement) {
        yield return assertStatement;
      }
      foreach (var assertStatementFromSubStatement in s.SubStatements.SelectMany(assertStatementsOfStatement)) {
        yield return assertStatementFromSubStatement;
      }
    }

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
            case Function f:
              if (f.Body is null) { break; }
              assertStatementsOfExpression(f.Body).ForEach(ReplaceExpressionInAssertStatement);
              break;
            case MethodOrConstructor mc:
              if (mc.Body is null) { break; }
              mc.Body.Body.SelectMany(assertStatementsOfStatement).ForEach(ReplaceExpressionInAssertStatement);
              break;
            default:
              throw new UnreachableException();
          }
        }
        break;
      case SubsetTypeDecl decl:
        assertStatementsOfExpression(decl.Constraint).ForEach(ReplaceExpressionInAssertStatement);
        if (decl.Witness is not null) {
          assertStatementsOfExpression(decl.Witness).ForEach(ReplaceExpressionInAssertStatement);
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
