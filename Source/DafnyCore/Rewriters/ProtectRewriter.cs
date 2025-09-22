#nullable disable
using Microsoft.Boogie;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;
public class ProtectRewriter(ErrorReporter r) : IRewriter(r) { // TODO: Figure out if the class can Extend Rewriter instead of IRewriter
  //MASSIVE TODOs:
  //  - figure out where you can call (some SystemModuleManager).CreateArrowTypeDecl(2) directly or deferred
  //  - actually do what ciobaca asked you to (search for something that can change an expression
  //    like a Substitutor and use it to present a way of protecting all Subclasses of Expression)

  //internal override void PreResolve(Program program) {
  //  program.SystemModuleManager.CreateArrowTypeDecl(2);// this doesn't work for some reason, prolly bcs it's done after parsing :(
  //}
  internal override void PreResolve(ModuleDefinition moduleDefinition) {
    if (moduleDefinition.EnclosingModule is null) {
      Contract.Assert(moduleDefinition.DefaultClass is not null);
      static Function protectorFunctionWithName(string name) {
        var typeVarForProtect = new TypeParameter(
          origin: SourceOrigin.NoToken,
          nameNode: new Name("T"),
          varianceSyntax: TPVarianceSyntax.NonVariant_Strict,
          characteristics: TypeParameterCharacteristics.Default(),
          typeBounds: [],
          attributes: null
        );
        return new(
          origin: SourceOrigin.NoToken,
          nameNode: new Name(name),
          hasStaticKeyword: false,
          isGhost: true,
          isOpaque: true,
          typeArgs: [typeVarForProtect],
          ins: [
            new Formal(
              origin: SourceOrigin.NoToken,
              nameNode: new Name("x"),
              syntacticType: new UserDefinedType(typeVarForProtect),
              inParam: true,
              isGhost: false,
              defaultValue: null,
              attributes: null,
              isOld: false,
              isNameOnly: false,
              isOlder: false,
              nameForCompilation: null
            ),
            new Formal(
              origin: SourceOrigin.NoToken,
              nameNode: new Name("name"),
              syntacticType: new UserDefinedType(
                origin: SourceOrigin.NoToken,
                name: "string",
                optTypeArgs: null
              ),
              inParam: true,
              isGhost: false,
              defaultValue: null,
              attributes: null,
              isOld: false,
              isNameOnly: false,
              isOlder: false,
              nameForCompilation: null
            )
          ],
          result: null,
          resultType: new UserDefinedType(typeVarForProtect),
          req: [],
          reads: new Specification<FrameExpression>(),
          ens: [],
          decreases: new Specification<Expression>(),
          body: new NameSegment(
            origin: SourceOrigin.NoToken,
            name: "x",
            optTypeArguments: null
          ),
          byMethodTok: null, byMethodBody: null,
          attributes: new Attributes(
            name: "auto_generated", args: [],
            prev: null
          ),
          signatureEllipsis: null
        );
      }
      moduleDefinition.DefaultClass.Members.AddRange(
        new string[] { "_protect", "_protectToProve", }.Select(protectorFunctionWithName)
      );
    }
    Contract.Assert(!moduleDefinition.TopLevelDecls.OfType<AbstractModuleDecl>().Any());
    Contract.Assert(!moduleDefinition.TopLevelDecls.Any(d => d is TypeParameter or AmbiguousTopLevelDecl));
    Contract.Assert(!moduleDefinition.TopLevelDecls.Any(d => d is InternalTypeSynonymDecl or NonNullTypeDecl));
    moduleDefinition.TopLevelDecls.Where(d => d is not ModuleDecl).ForEach(ApplyChangesTo);
  }

  private static ApplySuffix ExpressionWrappedInProtectCall(Expression expression) =>
    new(expression.Origin, null, new NameSegment(Token.NoToken, "_protect", null), [
      new ActualBinding(null, expression, false),
      new ActualBinding(null, new StringLiteralExpr(SourceOrigin.NoToken, expression.ToString(), false))
    ], null);

  private static Expression WithProtect(Expression expr) {
    //void simplerLog<T>(T e) where T: Expression { logNotImplementedMessage(e, nameof(T)); }
    void logNotImplementedMessage(Expression e, string name) {
      Console.WriteLine($"Dafny IPM: {name} not yet implemented.");
      Console.WriteLine(expr.ToString());
    }
    Contract.Requires(expr != null);
    //switch (expr) {
    //  case StaticReceiverExpr:
    //  case LiteralExpr:
    //  case DisplayExpression:
    //    return expr;
    //  default:
    //    Contract.Assert(false);
    //    break;
    //}
    if (expr is StaticReceiverExpr) {
      return expr;
    } else if (expr is LiteralExpr) {
      return expr;
      //return to_protect_call_on_expr(expr);
    } else if (expr is ThisExpr or IdentifierExpr or DatatypeValue) {
      return ExpressionWrappedInProtectCall(expr);
    } else if (expr is DisplayExpression) {
      logNotImplementedMessage(expr, "DisplayExpression");
      return expr;
    } else if (expr is MapDisplayExpr) {
      logNotImplementedMessage(expr, "MapDisplayExpr");
      return expr;
    } else if (expr is NameSegment) {
      return ExpressionWrappedInProtectCall(expr);
    } else if (expr is ExprDotName) {
      logNotImplementedMessage(expr, "ExprDotName");
      return expr;
    } else if (expr is ApplySuffix) {
      logNotImplementedMessage(expr, "ApplySuffix");
      return expr;
    } else if (expr is MemberSelectExpr) {
      logNotImplementedMessage(expr, "MemberSelectExpr");
      return expr;
    } else if (expr is SeqSelectExpr) {
      logNotImplementedMessage(expr, "SeqSelectExpr");
      return expr;
    } else if (expr is MultiSelectExpr) {
      logNotImplementedMessage(expr, "MultiSelectExpr");
      return expr;
    } else if (expr is SeqUpdateExpr) {
      logNotImplementedMessage(expr, "SeqUpdateExpr");
      return expr;
    } else if (expr is DatatypeUpdateExpr) {
      logNotImplementedMessage(expr, "DatatypeUpdateExpr");
      return expr;
    } else if (expr is ApplyExpr) {
      logNotImplementedMessage(expr, "ApplyExpr");
      return expr;
    } else if (expr is FunctionCallExpr) {
      logNotImplementedMessage(expr, "FunctionCallExpr");
      return expr;
    } else if (expr is SeqConstructionExpr) {
      logNotImplementedMessage(expr, "SeqConstructionExpr");
      return expr;
    } else if (expr is MultiSetFormingExpr) {
      logNotImplementedMessage(expr, "MultiSetFormingExpr");
      return expr;
    } else if (expr is OldExpr) {
      logNotImplementedMessage(expr, "OldExpr");
      return expr;
    } else if (expr is UnchangedExpr) {
      logNotImplementedMessage(expr, "UnchangedExpr");
      return expr;
    } else if (expr is FreshExpr) {
      logNotImplementedMessage(expr, "FreshExpr");
      return expr;
    } else if (expr is UnaryOpExpr) {
      var e = (UnaryOpExpr)expr;
      if (e.Op == UnaryOpExpr.Opcode.Cardinality) {
        Console.WriteLine("Dafny IPM: UnaryOpExpr.Opcode.Cardinality not yet implemented.");
        Console.WriteLine(expr.ToString());
        return expr;
      } else if (e.Op == UnaryOpExpr.Opcode.Allocated) {
        Console.WriteLine("Dafny IPM: UnaryOpExpr.Opcode.Allocated not yet implemented.");
        Console.WriteLine(expr.ToString());
        return expr;
      } else if (e.Op == UnaryOpExpr.Opcode.Lit) {
        Console.WriteLine("Dafny IPM: UnaryOpExpr.Opcode.Lit not yet implemented.");
        Console.WriteLine(expr.ToString());
        return expr;
      } else if (e.Op == UnaryOpExpr.Opcode.Assigned) {
        Console.WriteLine("Dafny IPM: UnaryOpExpr.Opcode.Assigned not yet implemented.");
        Console.WriteLine(expr.ToString());
        return expr;
      } else {
        Contract.Assert(e.Op != UnaryOpExpr.Opcode.Fresh); // this is handled is "is FreshExpr" case above
                                                           // Prefix operator.
                                                           // determine if parens are needed
        switch (e.Op) {
          case UnaryOpExpr.Opcode.Not:
            Console.WriteLine("Dafny IPM: UnaryOpExpr.Opcode.Not not yet implemented.");
            Console.WriteLine(expr.ToString());
            return expr;
          default:
            Contract.Assert(false);
            throw new Cce.UnreachableException(); // unexpected unary opcode
        }
      }
    } else if (expr is TypeUnaryExpr) {
      logNotImplementedMessage(expr, "TypeUnaryExpr");
      return expr;
    } else if (expr is BinaryExpr) {
      var e = expr as BinaryExpr;
      return new BinaryExpr(e.Origin, e.Op, WithProtect(e.E0), WithProtect(e.E1));
      // switch (e.Op)
      // {
      //   case BinaryExpr.Opcode.LeftShift:
      //   case BinaryExpr.Opcode.RightShift:
      //     opBindingStrength = BindingStrengthShift;
      //     fragileRightContext = true;
      //     break;
      //   case BinaryExpr.Opcode.Add:
      //     {
      //       opBindingStrength = BindingStrengthAdd;
      //       var t1 = e.E1.Type;
      //       fragileRightContext = t1 == null ||
      //                             !(t1.IsIntegerType || t1.IsRealType || t1.IsBigOrdinalType || t1.IsBitVectorType);
      //       break;
      //     }
      //   case BinaryExpr.Opcode.Sub:
      //     opBindingStrength = BindingStrengthAdd;
      //     fragileRightContext = true;
      //     break;
      //   case BinaryExpr.Opcode.Mul:
      //     {
      //       opBindingStrength = BindingStrengthMul;
      //       var t1 = e.E1.Type;
      //       fragileRightContext = t1 == null ||
      //                             !(t1.IsIntegerType || t1.IsRealType || t1.IsBigOrdinalType || t1.IsBitVectorType);
      //       break;
      //     }
      //   case BinaryExpr.Opcode.Div:
      //   case BinaryExpr.Opcode.Mod:
      //     opBindingStrength = BindingStrengthMul;
      //     fragileRightContext = true;
      //     break;
      //   case BinaryExpr.Opcode.BitwiseAnd:
      //     opBindingStrength = BindingStrengthBitwiseAnd; break;
      //   case BinaryExpr.Opcode.BitwiseOr:
      //     opBindingStrength = BindingStrengthBitwiseOr; break;
      //   case BinaryExpr.Opcode.BitwiseXor:
      //     opBindingStrength = BindingStrengthBitwiseXor; break;
      //   case BinaryExpr.Opcode.Eq:
      //   case BinaryExpr.Opcode.Neq:
      //   case BinaryExpr.Opcode.Gt:
      //   case BinaryExpr.Opcode.Ge:
      //   case BinaryExpr.Opcode.Lt:
      //   case BinaryExpr.Opcode.Le:
      //   case BinaryExpr.Opcode.Disjoint:
      //   case BinaryExpr.Opcode.In:
      //   case BinaryExpr.Opcode.NotIn:
      //     opBindingStrength = BindingStrengthCompare;
      //     fragileLeftContext = fragileRightContext = true;
      //     break;
      //   case BinaryExpr.Opcode.And:
      //     opBindingStrength = BindingStrengthAnd; break;
      //   case BinaryExpr.Opcode.Or:
      //     opBindingStrength = BindingStrengthOr; break;
      //   case BinaryExpr.Opcode.Imp:
      //     opBindingStrength = BindingStrengthImplies;
      //     fragileLeftContext = true;
      //     break;
      //   case BinaryExpr.Opcode.Exp:
      //     opBindingStrength = BindingStrengthExplies;
      //     fragileRightContext = true;
      //     break;
      //   case BinaryExpr.Opcode.Iff:
      //     opBindingStrength = BindingStrengthEquiv; break;
      //   default:
      //     Contract.Assert(false);
      //     throw new Cce.UnreachableException(); // unexpected binary operator
      // }

      // bool parensNeeded = ParensNeeded(opBindingStrength, contextBindingStrength, fragileContext);

      // string op = BinaryExpr.OpcodeString(e.Op);
      // if (parensNeeded)
      // {
      //   wr.Write("(");
      // }

      // var sem = !parensNeeded && isFollowedBySemicolon;
      // if (0 <= indent && e.Op == BinaryExpr.Opcode.And)
      // {
      //   PrintExpr(e.E0, opBindingStrength, fragileLeftContext, false, sem, indent, keyword);
      //   wr.WriteLine(" {0}", op);
      //   Indent(indent);
      //   PrintExpr(e.E1, opBindingStrength, fragileRightContext, parensNeeded || isRightmost, sem, indent, keyword);
      // }
      // else if (0 <= indent && e.Op == BinaryExpr.Opcode.Imp)
      // {
      //   PrintExpr(e.E0, opBindingStrength, fragileLeftContext, false, sem, indent, keyword);
      //   wr.WriteLine(" {0}", op);
      //   int ind = indent + IndentAmount;
      //   Indent(ind);
      //   PrintExpr(e.E1, opBindingStrength, fragileRightContext, parensNeeded || isRightmost, sem, ind, keyword);
      // }
      // else if (0 <= indent && e.Op == BinaryExpr.Opcode.Exp)
      // {
      //   PrintExpr(e.E1, opBindingStrength, fragileLeftContext, false, sem, indent, keyword);
      //   wr.WriteLine(" {0}", op);
      //   int ind = indent + IndentAmount;
      //   Indent(ind);
      //   PrintExpr(e.E0, opBindingStrength, fragileRightContext, parensNeeded || isRightmost, sem, ind, keyword);
      // }
      // else if (e.Op == BinaryExpr.Opcode.Exp)
      // {
      //   PrintExpr(e.E1, opBindingStrength, fragileLeftContext, false, sem, -1, keyword);
      //   wr.Write(" {0} ", op);
      //   PrintExpr(e.E0, opBindingStrength, fragileRightContext, parensNeeded || isRightmost, sem, -1, keyword);
      // }
      // else
      // {
      //   PrintExpr(e.E0, opBindingStrength, fragileLeftContext, false, sem, -1, keyword);
      //   wr.Write(" {0} ", op);
      //   PrintExpr(e.E1, opBindingStrength, fragileRightContext, parensNeeded || isRightmost, sem, -1, keyword);
      // }

      // if (parensNeeded)
      // {
      //   wr.Write(")");
      // }
    } else if (expr is TernaryExpr) {
      logNotImplementedMessage(expr, "TernaryExpr");
      return expr;
      // var e = (TernaryExpr)expr;
      // switch (e.Op)
      // {
      //   case TernaryExpr.Opcode.PrefixEqOp:
      //   case TernaryExpr.Opcode.PrefixNeqOp:
      //     var opBindingStrength = BindingStrengthCompare;
      //     var fragileLeftContext = true;
      //     var fragileRightContext = true;
      //     bool parensNeeded = ParensNeeded(opBindingStrength, contextBindingStrength, fragileContext);

      //     if (parensNeeded)
      //     {
      //       wr.Write("(");
      //     }

      //     var sem = !parensNeeded && isFollowedBySemicolon;
      //     PrintExpr(e.E1, opBindingStrength, fragileLeftContext, false, sem, -1, keyword);
      //     wr.Write(" {0}#[", e.Op == TernaryExpr.Opcode.PrefixEqOp ? "==" : "!=");
      //     PrintExpression(e.E0, false);
      //     wr.Write("] ");
      //     PrintExpr(e.E2, opBindingStrength, fragileRightContext, parensNeeded || isRightmost, sem, -1, keyword);
      //     if (parensNeeded)
      //     {
      //       wr.Write(")");
      //     }

      //     break;
      //   default:
      //     Contract.Assert(false); // unexpected ternary operator
      //     break;
      // }
    } else if (expr is ChainingExpression) {
      var e = expr as ChainingExpression;
      if (e.PrefixLimits.Any(pl => pl != null)) {
        logNotImplementedMessage(expr, "ChainingExpression prefixLimits");
        return expr;
      }
      return new ChainingExpression(e.Origin, [.. e.Operands.Select(o => WithProtect(o))], e.Operators, e.OperatorLocs, e.PrefixLimits);
      // // determine if parens are needed
      // int opBindingStrength = BindingStrengthCompare;
      // bool parensNeeded = ParensNeeded(opBindingStrength, contextBindingStrength, fragileContext);

      // if (parensNeeded)
      // {
      //   wr.Write("(");
      // }

      // var sem = !parensNeeded && isFollowedBySemicolon;
      // PrintExpr(e.Operands[0], opBindingStrength, true, false, sem, -1, keyword);
      // for (int i = 0; i < e.Operators.Count; i++)
      // {
      //   string op = BinaryExpr.OpcodeString(e.Operators[i]);
      //   if (e.PrefixLimits[i] == null)
      //   {
      //     wr.Write(" {0} ", op);
      //   }
      //   else
      //   {
      //     wr.Write(" {0}#[", op);
      //     PrintExpression(e.PrefixLimits[i], false);
      //     wr.Write("] ");
      //   }

      //   PrintExpr(e.Operands[i + 1], opBindingStrength, true,
      //     i == e.Operators.Count - 1 && (parensNeeded || isRightmost), sem, -1, keyword);
      // }

      // if (parensNeeded)
      // {
      //   wr.Write(")");
      // }
    } else if (expr is LetExpr) {
      logNotImplementedMessage(expr, "LetExpr");
      return expr;
    } else if (expr is LetOrFailExpr) {
      logNotImplementedMessage(expr, "LetOrFailExpr");
      return expr;
    } else if (expr is QuantifierExpr) {
      logNotImplementedMessage(expr, "QuantifierExpr");
      return expr;
    } else if (expr is SetComprehension) {
      logNotImplementedMessage(expr, "SetComprehension");
      return expr;
    } else if (expr is MapComprehension) {
      logNotImplementedMessage(expr, "MapComprehension");
      return expr;
    } else if (expr is LambdaExpr) {
      logNotImplementedMessage(expr, "LambdaExpr");
      return expr;
    } else if (expr is WildcardExpr) {
      logNotImplementedMessage(expr, "WildcardExpr");
      return expr;
    } else if (expr is StmtExpr) {
      logNotImplementedMessage(expr, "StmtExpr");
      return expr;
    } else if (expr is ITEExpr) {
      logNotImplementedMessage(expr, "ITEExpr");
      return expr;
    } else if (expr is ParensExpression) {
      logNotImplementedMessage(expr, "ParensExpression");
      return expr;
    } else if (expr is NegationExpression) {
      logNotImplementedMessage(expr, "NegationExpression");
      return expr;
    } else if (expr is NestedMatchExpr) {
      logNotImplementedMessage(expr, "NestedMatchExpr");
      return expr;
    } else if (expr is MatchExpr) {
      logNotImplementedMessage(expr, "MatchExpr");
      return expr;
    } else if (expr is DefaultValueExpression) {
      // DefaultValueExpression's are introduced during resolution, so we expect .Resolved to be non-null
      Contract.Assert(expr.WasResolved());
      Contract.Assert(expr.Resolved != null);
      logNotImplementedMessage(expr, "DefaultValueExpression");
      return expr;
    } else if (expr is BoxingCastExpr) {
      logNotImplementedMessage(expr, "BoxingCastExpr");
      return expr;
    } else if (expr is BoogieGenerator.BoogieWrapper) {
      logNotImplementedMessage(expr, "BoogieGenerator.BoogieWrapper");
      return expr;
    } else if (expr is BoogieGenerator.BoogieFunctionCall) {
      logNotImplementedMessage(expr, "BoogieGenerator.BoogieFunctionCall");
      return expr;
    } else if (expr is ResolverIdentifierExpr) {
      logNotImplementedMessage(expr, "ResolverIdentifierExpr");
      return expr;
    } else if (expr is DecreasesToExpr) {
      logNotImplementedMessage(expr, "DecreasesToExpr");
      return expr;
    } else if (expr is IndexFieldLocationExpression) {
      logNotImplementedMessage(expr, "IndexFieldLocationExpression");
      return expr;
    } else if (expr is FieldLocationExpression) {
      logNotImplementedMessage(expr, "FieldLocationExpression");
      return expr;
    } else if (expr is FieldLocation) {
      logNotImplementedMessage(expr, "FieldLocation");
      return expr;
    } else if (expr is IndexFieldLocation) {
      logNotImplementedMessage(expr, "IndexFieldLocation");
      return expr;
    } else if (expr is LocalsObjectExpression) {
      logNotImplementedMessage(expr, "LocalsObjectExpression");
      return expr;
    } else {
      Console.WriteLine("Dafny IPM: Unexpected expression type.");
      Console.WriteLine(expr.ToString());
      Contract.Assert(false);
      return expr;
    }
  }

  private static Expression WithProtectToProve(Expression e) =>
    new ApplySuffix(e.Origin, null, new NameSegment(Token.NoToken, "_protectToProve", null), [
      new ActualBinding(null, WithProtect(e), false),
      new ActualBinding(null, new StringLiteralExpr(SourceOrigin.NoToken, e.ToString(), false))
    ], null);

  private static void ApplyChangesTo(TopLevelDecl d) {
    static IEnumerable<AssertStmt> assertStatementsOfExpression(Expression e) {
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
      if (Attributes.Contains(a.Attributes, "itp")) {
        Console.WriteLine("Protecting to prove assertion " + a.Expr.ToString());
        a.Expr = WithProtectToProve(a.Expr);
      } else {
        a.Expr = WithProtect(a.Expr);
      }
    }
    
    switch (d) {
      case TopLevelDeclWithMembers decl:
        foreach (var member in decl.Members.OfType<MethodOrFunction>()) {
          foreach (var req in member.Req) {
            req.E = WithProtect(req.E);
          }
          foreach (var ens in member.Ens) {
            if (Attributes.Contains(ens.Attributes, "itp")) {
              Console.WriteLine("Protecting to prove ensures clause" + ens.E.ToString());
              ens.E = WithProtectToProve(ens.E);
            } else {
              ens.E = WithProtect(ens.E);
            }
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
            //case Constructor c:
            //  if (c.Body is null) { break; }
            //  c.Body.Body.SelectMany(assertStatementsOfStatement).ForEach(ReplaceExpressionInAssertStatement);
            //  break;
            //case Method m:
            //  if (m.Body is null) { break; }
            //  m.Body.Body.SelectMany(assertStatementsOfStatement).ForEach(ReplaceExpressionInAssertStatement);
            //  break;
            default: throw new UnreachableException();
          }
        }
        break;
      case SubsetTypeDecl decl:
        assertStatementsOfExpression(decl.Constraint).ForEach(ReplaceExpressionInAssertStatement);
        if (decl.Witness is not null) {
          assertStatementsOfExpression(decl.Witness).ForEach(ReplaceExpressionInAssertStatement);
        }
        break;
      case ConcreteTypeSynonymDecl: break;
      default: throw new UnreachableException();
    }
  }
}
