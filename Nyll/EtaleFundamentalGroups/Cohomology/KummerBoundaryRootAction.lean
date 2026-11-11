/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnity
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionPullback
public import Nyll.EtaleFundamentalGroups.Cohomology.FiberTranslation
public import Nyll.EtaleFundamentalGroups.Cohomology.KummerBoundaryRoots

/-!
# Original coefficient translation is multiplication of actual roots

Translation on the original Kummer boundary lift sheaf multiplies its
actual root coordinate by the same coefficient through the original
structural map. The actual root coordinate also detects equality of
sections. These statements retain the original extension and its
specified roots-of-unity kernel identification.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian
open EtaleCohomology

namespace EtaleFundamentalGroups.Cohomology

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  (c : X ⟶ Spec (.of K)) {n : ℕ} (hn : 0 < n) (hnK : IsUnit (n : K))

/-- The actual Kummer root coordinate determines its original lift
section, including the actual integer-one quotient coordinate. -/
theorem constantKummerBoundaryRoot_injective
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0) (V : X.Etale) :
    Function.Injective (constantKummerBoundaryRoot c hn hnK a V) := by
  intro s t h
  apply (constantKummerBoundaryRootEquiv c hn hnK a V).injective
  apply Subtype.ext
  exact (constantKummerBoundaryRootEquiv_val c hn hnK a V s).trans
    (h.trans (constantKummerBoundaryRootEquiv_val c hn hnK a V t).symm)

/-- Original constant coefficient translation is multiplication by
that same root of unity through the actual structural ring map. -/
theorem constantKummerBoundaryRoot_translation
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0) (V : X.Etale)
    (s : (extensionFiber (constantKummerBoundaryExtension c hn hnK a)
      (integerUnitSection X)).obj.obj (op V)) (ζ : rootsOfUnity n K) :
    let P := constantKummerBoundaryExtension c hn hnK a
    constantKummerBoundaryRoot c hn hnK a V
        ((constantFiberTranslation (AddCommGrpCat.of (Additive (rootsOfUnity n K)))
          P.f P.g P.zero (integerUnitSection X) (Additive.ofMul ζ)).hom.app (op V) s) =
      Units.map (((Scheme.ΓSpecIso (.of K)).inv ≫
        ((show V.left ⟶ X from V.hom) ≫ c).appTop).hom.toMonoidHom)
          (ζ : Kˣ) * constantKummerBoundaryRoot c hn hnK a V s := by
  intro P
  let η : P.X₁.obj.obj (op V) :=
    (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj
      (AddCommGrpCat.of (Additive (rootsOfUnity n K))))).app (op V) (Additive.ofMul ζ)
  let p : P.X₂ ⟶ etaleMultiplicativeGroupSheaf X :=
    pullback.fst (etaleMultiplicativeGroupPower X n) (Ext.addEquiv₀ a)
  let q : P.X₂.obj.obj (op V) →+ Additive ((Γ(V.left, ⊤) : Type u)ˣ) :=
    (etaleMultiplicativeGroupSectionsEquiv X V).toAddMonoidHom.comp
      (p.hom.app (op V)).hom
  let s₀ : P.X₂.obj.obj (op V) := s.val
  let z : (Γ(V.left, ⊤) : Type u)ˣ :=
    Units.map (((Scheme.ΓSpecIso (.of K)).inv ≫
      ((show V.left ⟶ X from V.hom) ≫ c).appTop).hom.toMonoidHom) (ζ : Kˣ)
  have hi := ConcreteCategory.congr_hom
    (congrArg (fun f : P.X₁ ⟶ etaleMultiplicativeGroupSheaf X => f.hom.app (op V))
      (coefficientPullbackExtension_f_fst (etaleKummerComplex X n)
        (constantRootsOfUnityKummerKernelIso c hn hnK) (Ext.addEquiv₀ a))) η
  have hscalar₀ : p.hom.app (op V) (P.f.hom.app (op V) η) = Additive.ofMul z :=
    hi.trans (constantRootsOfUnityKummerKernelIso_generator c hn hnK V ζ)
  have hscalar : q (P.f.hom.app (op V) η) = Additive.ofMul z :=
    congrArg (etaleMultiplicativeGroupSectionsEquiv X V) hscalar₀
  change (q (P.f.hom.app (op V) η + s₀)).toMul = z * (q s₀).toMul
  rw [map_add, hscalar]
  rfl

end EtaleFundamentalGroups.Cohomology
