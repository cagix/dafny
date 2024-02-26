using System.Collections.Generic;

namespace Microsoft.Dafny;

public abstract class MethodOrFunction : MemberDecl {
  public readonly List<TypeParameter> TypeArgs;
  public readonly List<AttributedExpression> Req;
  public readonly List<AttributedExpression> Ens;
  public readonly Specification<Expression> Decreases;

  protected MethodOrFunction(RangeToken rangeToken, Name name, bool hasStaticKeyword, bool isGhost,
    Attributes attributes, bool isRefining, List<TypeParameter> typeArgs,
    List<AttributedExpression> req,
    List<AttributedExpression> ens,
    Specification<Expression> decreases)
    : base(rangeToken, name, hasStaticKeyword, isGhost, attributes, isRefining) {
    TypeArgs = typeArgs;
    Req = req;
    Decreases = decreases;
    Ens = ens;
  }

  protected MethodOrFunction(Cloner cloner, MethodOrFunction original) : base(cloner, original) {
    this.TypeArgs = cloner.CloneResolvedFields ? original.TypeArgs : original.TypeArgs.ConvertAll(cloner.CloneTypeParam);
    this.Req = original.Req.ConvertAll(cloner.CloneAttributedExpr);
    this.Decreases = cloner.CloneSpecExpr(original.Decreases);
    this.Ens = original.Ens.ConvertAll(cloner.CloneAttributedExpr);
  }

  protected abstract bool Bodyless { get; }
  protected abstract string TypeName { get; }

  public bool IsVirtual => EnclosingClass is TraitDecl && !IsStatic;
  public bool IsAbstract => EnclosingClass.EnclosingModuleDefinition.ModuleKind != ModuleKindEnum.Concrete;

  public virtual void Resolve(ModuleResolver resolver) {
    if (Bodyless && !IsVirtual && !IsAbstract && !this.IsExtern(resolver.Options) && !this.IsExplicitAxiom()) {
      foreach (var ensures in Ens) {
        if (!ensures.IsExplicitAxiom() && !resolver.Options.Get(CommonOptionBag.AllowAxioms)) {
          resolver.Reporter.Warning(MessageSource.Verifier, ResolutionErrors.ErrorId.none, ensures.Tok,
            $"This ensures clause is part of a bodyless {TypeName}. Add the {{:axiom}} attribute to it or the enclosing {TypeName} to suppress this warning");
        }
      }
    }
  }

  protected MethodOrFunction(RangeToken tok, Name name, bool hasStaticKeyword, bool isGhost, Attributes attributes, bool isRefining) : base(tok, name, hasStaticKeyword, isGhost, attributes, isRefining) {
  }
}