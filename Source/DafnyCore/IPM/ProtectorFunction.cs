#nullable enable
using Microsoft.Dafny;
using System.Collections.Generic;

namespace DafnyCore.IPM {
  public class ProtectorFunction : Function {
    #region init helpers
    protected ProtectorFunction(List<TypeParameter> typeArgs, string name, (List<Formal> args, Type result) signature, Expression body) : base(
      origin: new Token(),
      // can't use SourceOrigin.NoToken because ref. eq. to it
      // is used to ensure that DefaultModuleDefinitions are verified;
      // I do NOT like that piece of code (:
      nameNode: new(name),
      hasStaticKeyword: false,
      isGhost: true,
      isOpaque: true,
      typeArgs: typeArgs,
      ins: signature.args,
      result: null,
      resultType: signature.result,
      req: [],
      reads: new(),
      ens: [],
      decreases: new(),
      body: body,
      byMethodTok: null, byMethodBody: null,
      attributes: new(
        name: "auto_generated", args: [],
        prev: null
      ),
      signatureEllipsis: null
    ) { }
    protected static TypeParameter SimpleTypeVar(string name) => new(
      origin: SourceOrigin.NoToken,
      nameNode: new(name),
      varianceSyntax: TPVarianceSyntax.NonVariant_Strict,
      characteristics: TypeParameterCharacteristics.Default(),
      typeBounds: [],
      attributes: null
    );
    private static Formal SimpleFormalCommon(string name, Type type) => new(
      origin: SourceOrigin.NoToken,
      nameNode: new(name),
      syntacticType: type,
      inParam: true,
      isGhost: false,
      defaultValue: null,
      attributes: null,
      isOld: false,
      isNameOnly: false,
      isOlder: false,
      nameForCompilation: null
    );
    protected static Formal SimpleFormal(string name, TypeParameter typeVar) => SimpleFormalCommon(name, new UserDefinedType(typeVar));
    protected static Type StringType() => new UserDefinedType(origin: SourceOrigin.NoToken, name: "string", optTypeArgs: null);
    protected static Formal SimpleFormal(string name, Type type) => SimpleFormalCommon(name, type);
    protected static Expression BodyFromFormal(Formal f) => new NameSegment(
      origin: SourceOrigin.NoToken,
      name: f.Name,
      optTypeArguments: null
    );
    #endregion
  }
  public class ProtectFunction : ProtectorFunction {
    public static readonly string ProtectorFunctionName = "_protect";
    private ProtectFunction(TypeParameter typeVar, Formal firstArg) : base(
      typeArgs: [typeVar,],
      name: ProtectorFunctionName,
      signature: ([
        firstArg,
        SimpleFormal("name", StringType()),
      ], new UserDefinedType(typeVar)),
      body: BodyFromFormal(firstArg)
    ) { }
    private ProtectFunction(TypeParameter typeVar) : this(typeVar, SimpleFormal("x", typeVar)) { }
    public ProtectFunction() : this(SimpleTypeVar("T")) { }

    public static ApplySuffix CallOn(Expression expression) => new(expression.Origin, null, new NameSegment(SourceOrigin.NoToken, ProtectorFunctionName, null), [
      new(null, expression),
      new(null, new StringLiteralExpr(SourceOrigin.NoToken, expression.ToString(), false)),
    ], Token.NoToken);
  }
  public class ProtectScopeFunction : ProtectorFunction {
    public static readonly string ProtectorFunctionName = "_protectScope";
    private ProtectScopeFunction(TypeParameter typeVar) : base(
      typeArgs: [typeVar,],
      name: ProtectorFunctionName,
      signature: ([
        SimpleFormal("x", typeVar),
        SimpleFormal("name", StringType()),
      ], new BoolType()),
      body: new LiteralExpr(
        origin: SourceOrigin.NoToken,
        value: true
      )
    ) { }
    public ProtectScopeFunction() : this(SimpleTypeVar("T")) { }
    
    public static ApplySuffix CallOn(string varname) => new(SourceOrigin.NoToken, null, new NameSegment(SourceOrigin.NoToken, ProtectorFunctionName, null), [
      new(null, new NameSegment(SourceOrigin.NoToken, varname, null)),
      new(null, new StringLiteralExpr(SourceOrigin.NoToken, varname, false)),
    ], Token.NoToken);
  }
  public class ProtectToProveFunction : ProtectorFunction {
    public static readonly string ProtectorFunctionName = "_protectToProve";
    private ProtectToProveFunction(TypeParameter typeVar, Formal firstArg) : base(
      typeArgs: [typeVar,],
      name: ProtectorFunctionName,
      signature: ([
        firstArg,
        SimpleFormal("name", StringType()),
        SimpleFormal("scope", new SeqType(new BoolType())),
      ], new UserDefinedType(typeVar)),
      body: BodyFromFormal(firstArg)
    ) { }
    private ProtectToProveFunction(TypeParameter typeVar) : this(typeVar, SimpleFormal("x", typeVar)) { }
    public ProtectToProveFunction() : this(SimpleTypeVar("T")) { }

    public static ApplySuffix CallOn(Expression expression) => new ProtectToProveApplySuffix(expression);
  }
}
