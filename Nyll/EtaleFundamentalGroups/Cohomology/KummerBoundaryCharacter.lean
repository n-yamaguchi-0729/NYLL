/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnity
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernel
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionMonodromyDisplacement
public import Nyll.EtaleFundamentalGroups.Cohomology.KummerBoundaryExtension
public import Nyll.EtaleFundamentalGroups.Cohomology.KummerBoundaryMonodromyRoots
public import Nyll.EtaleFundamentalGroups.Cohomology.H1Character

/-!
# The original Kummer boundary character on actual roots

The canonical character of the original degree-zero Kummer boundary,
with the original constant-root coefficients, sends an actual root to
its original Galois conjugate by multiplication by its character value.
The root is evaluated on the actual finite étale representing cover.
Both the character comparison and its field action are proved from the
original extension and scheme maps.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian
open EtaleCohomology

namespace EtaleFundamentalGroups.Cohomology

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  [IsIntegral X] (c : X ⟶ Spec (.of K))
  {n : ℕ} [NeZero n] (hn : 0 < n) (hnK : IsUnit (n : K))
  (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0)

local notation "A" => AddCommGrpCat.of (Additive (rootsOfUnity n K))
local notation "P" => constantKummerBoundaryExtension c hn hnK a
local notation "hP" => constantKummerBoundaryExtension_shortExact c hn hnK a
local notation "b" => Sheaf.H.map (Iso.inv (constantRootsOfUnityKummerKernelIso c hn hnK)) 1
  (Sheaf.H.δ (etaleKummerComplex_shortExact X hn
    (etaleKummerExponentUnit_of_base c hnK)) 0 1 rfl a)

/-- The original finite H¹ character of a genuine Kummer boundary
multiplies an actual root by precisely its original Galois quotient. -/
theorem h1Character_constantKummerBoundary_fieldSource_root
    (F Ω : Type u) [Field F] [Field Ω] [Algebra F Ω]
    [IsSepClosure F Ω] [IsSepClosed Ω]
    (j : Spec (.of F) ⟶ X) (σ : Gal(Ω/F))
    (q : (extensionMonodromy A (P).f (P).g (P).zero hP (integerUnitSection X)
      (Spec.algebraMap F Ω ≫ j)).obj.V) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    Units.map (((Scheme.ΓSpecIso (.of K)).inv ≫
      ((Spec.algebraMap F Ω ≫ j) ≫ c).appTop ≫
        (Scheme.ΓSpecIso (.of Ω)).hom).hom.toMonoidHom)
      ((h1Character A (Spec.algebraMap F Ω ≫ j) b
        (FiniteEtale.fieldSourceAbsoluteGaloisHom F Ω j σ)).toAdd.toMul :
          rootsOfUnity n K).val *
        constantKummerBoundaryMonodromyRoot c hn hnK a (Spec.algebraMap F Ω ≫ j) q =
      Units.map σ.toRingHom.toMonoidHom
        (constantKummerBoundaryMonodromyRoot c hn hnK a (Spec.algebraMap F Ω ≫ j) q) := by
  intro coefficientTopology
  let ξ := Spec.algebraMap F Ω ≫ j
  let g := FiniteEtale.fieldSourceAbsoluteGaloisHom F Ω j σ
  let χ := extensionMonodromyCharacter A (P).f (P).g (P).zero hP (integerUnitSection X) ξ
  let coefficientTorsor :=
    extensionMonodromyTorsor A (P).f (P).g (P).zero hP (integerUnitSection X) ξ
  let ζ : rootsOfUnity n K := (χ g).toAdd.toMul
  rw [h1Character_constantKummerBoundary c hn hnK ξ a]
  have hroot := constantKummerBoundaryMonodromyRoot_translation c hn hnK a ξ ζ q
  have hdisp := extensionMonodromyCharacter_smul
    A (P).f (P).g (P).zero hP (integerUnitSection X) ξ g q
  calc
    Units.map (((Scheme.ΓSpecIso (.of K)).inv ≫ (ξ ≫ c).appTop ≫
        (Scheme.ΓSpecIso (.of Ω)).hom).hom.toMonoidHom) (ζ : Kˣ) *
          constantKummerBoundaryMonodromyRoot c hn hnK a ξ q =
      constantKummerBoundaryMonodromyRoot c hn hnK a ξ (χ g • q) := hroot.symm
    _ = constantKummerBoundaryMonodromyRoot c hn hnK a ξ (g • q) :=
      congrArg (constantKummerBoundaryMonodromyRoot c hn hnK a ξ) hdisp
    _ = Units.map σ.toRingHom.toMonoidHom
        (constantKummerBoundaryMonodromyRoot c hn hnK a ξ q) :=
      constantKummerBoundaryMonodromyRoot_fieldSource c hn hnK a F Ω j σ q

end EtaleFundamentalGroups.Cohomology
