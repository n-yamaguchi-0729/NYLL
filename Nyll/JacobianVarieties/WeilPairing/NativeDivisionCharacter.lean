/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.KummerEvaluationUnits
import Nyll.EtaleCohomology.Classical.GenericUnitCohomology
import Nyll.EtaleFundamentalGroups.Cohomology.ConstantGenericKummerDivisorExtension
import Nyll.EtaleFundamentalGroups.Cohomology.GenericKummerDivisorCharacter
import Nyll.EtaleFundamentalGroups.Cohomology.GenericKummerDivisorMonodromyRoots
import Nyll.EtaleFundamentalGroups.Cohomology.H1Character
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisPoint
import Nyll.JacobianVarieties.WeilPairing.DivisionDifference
import Nyll.JacobianVarieties.WeilPairing.NativePointedDivisionEvaluation
import Nyll.SchemeTheory.FunctionFields.StructureMorphism

/-!
# The native H¹ character of a division evaluation

The original pointed division evaluations construct a point of the actual
native Kummer fiber. Its original H¹ character acts on the evaluated root
by the field automorphism. The common normalization comes from the ground
field and is fixed, so the quotient is the divisorial Weil pairing of the
semilinear division difference.

The geometric-point field may be an algebraic closure in positive
characteristic. It is not also required to be a separable closure of the
function field. This identifies the original H¹ character, but does not
identify the degree of the original H¹ cup product with the Weil pairing.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory Limits AlgebraicCurve
open EtaleCohomology EtaleFundamentalGroups.Cohomology
open scoped Pointwise

namespace JacobianVarieties.WeilPairing

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of K))
  {n : ℕ} [NeZero n] (hn : 0 < n) (hnK : IsUnit (n : K))
  (d : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0)
  (b : Sheaf.H.{u} (etaleGenericUnitShortComplex X).X₂ 0)
  (hb : Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 b = n • d)
  (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra X.functionField Ω]
  {F : Type v} [Field F] [Algebra Ω F]
  [Algebra (RatFunc Ω) F] [IsScalarTower Ω (RatFunc Ω) F]
  [FiniteDimensional (RatFunc Ω) F] [HasPrincipalDivisors Ω F]

local notation "j" => X.fromSpecStalk (genericPoint X)
local notation "η" => Spec.algebraMap X.functionField Ω
local notation "ξ" => η ≫ j
local notation "A" => AddCommGrpCat.of (Additive (rootsOfUnity n K))
local notation "hP" => constantGenericKummerDivisorExtension_shortExact c hn hnK d b hb
local notation "r" => genericKummerDivisorMonodromyRoot c hn hnK d b hb Ω
local notation "ι" =>
  CommRingCat.Hom.hom
    (Iso.inv (Scheme.ΓSpecIso (CommRingCat.of K)) ≫ Scheme.Hom.appTop (ξ ≫ c) ≫
      Iso.hom (Scheme.ΓSpecIso (CommRingCat.of Ω)))
local notation "a" => Units.map (RingHom.toMonoidHom (algebraMap X.functionField Ω))
  (Additive.toMul (genericPointUnitsH0Equiv X b))

omit [IsAlgClosed K] [IsAlgClosed Ω] in
private theorem genericStructuralScalar_fixed
    (σ : Ω ≃ₐ[X.functionField] Ω) (s : K) : σ (ι s) = ι s := by
  have hbase : ξ ≫ c = Spec.map (CommRingCat.ofHom
      ((algebraMap X.functionField Ω).comp (baseToFunctionField c))) := by
    rw [Category.assoc, fromSpecStalk_genericPoint_comp_base, ← Spec.map_comp]
    rfl
  have hι : ι = (algebraMap X.functionField Ω).comp (baseToFunctionField c) := by
    rw [hbase, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc, CommRingCat.hom_ofHom]
  rw [hι]
  exact σ.commutes (baseToFunctionField c s)

/-- The actual native H¹ character is the Weil pairing of a semilinear
division difference. The evaluation root and its ground-field normalization
are constructed from the pointed divisor data, in every characteristic. -/
theorem exists_nativePointedWeilDatum_pairing_eq_h1Character
    (D E : Divisor Ω F) (x ε : Place Ω F) (f g : F)
    (hf : f ≠ 0) (hg : g ≠ 0)
    (hfdiv : ∀ w : Place Ω F, w.ord f = (n : ℤ) * D w)
    (hgdiv : ∀ w : Place Ω F, w.ord g = (n : ℤ) * E w -
      (Finsupp.single x 1 + Finsupp.single ε (-1) : Divisor Ω F) w)
    (hDE : ∀ w : Place Ω F, D w = 0 ∨ E w = 0)
    (hDx : D x = 0) (hDε : D ε = 0)
    (a₀ : Kˣ) (hx : x.evalAt f = (a : Ω)) (hε : ε.evalAt f = ι (a₀ : K))
    (σ : Ω ≃ₐ[X.functionField] Ω) (θ : SemilinearAut Ω F)
    (hθbase : SemilinearAut.baseAut θ = σ.toRingEquiv)
    (hθf : θ • f = f) (hθD : θ • D = D)
    (hθB : θ • (Finsupp.single x 1 + Finsupp.single ε (-1) : Divisor Ω F) =
      Finsupp.single x 1 + Finsupp.single ε (-1)) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    ∃ w : WeilDatum Ω F n,
      w.D₁ = D ∧ w.D₂ = θ • E - E ∧ w.f₁ = f ∧ w.f₂ = (θ • g) / g ∧
      w.pairing = ι (Units.val ((rootsOfUnity n K).subtype
        (Additive.toMul (α := rootsOfUnity n K)
          ((h1Character A ξ
            (constantGenericKummerDivisorExtension_shortExact c hn hnK d b hb).extClass
            (FiniteEtale.fundamentalGroupHom j η
              (FiniteEtale.fieldAutomorphismFiberAction X.functionField Ω σ))).toAdd)))) := by
  intro coefficientTopology
  obtain ⟨s, _, q, _, hq, _, _⟩ := exists_nativePointedDivisionEvaluation
    c hn hnK d b hb Ω D E E x ε f g g hf hg hg hfdiv hgdiv hgdiv
      hDE hDE hDx hDε a₀ hx hε
  let B : Divisor Ω F := Finsupp.single x 1 + Finsupp.single ε (-1)
  have hDB : ∀ w : Place Ω F, D w = 0 ∨ B w = 0 := by
    intro w
    by_cases hw : D w = 0
    · exact Or.inl hw
    · have hwx : w ≠ x := fun h => hw ((congrArg D h).trans hDx)
      have hwε : w ≠ ε := fun h => hw ((congrArg D h).trans hDε)
      exact Or.inr (by
        change (Finsupp.single x 1 + Finsupp.single ε (-1) : Divisor Ω F) w = 0
        rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hwx,
          Finsupp.single_eq_of_ne hwε, add_zero])
  obtain ⟨w, hD₁, hD₂, hf₁, hf₂, hpair⟩ :=
    WeilDatum.exists_semilinearDivisionDifference n D E B f g hf hg
      hfdiv hgdiv hDE hDB θ hθf hθD hθB
      (fun w _ => w.isRational_of_isAlgClosed) (fun w _ => w.isRational_of_isAlgClosed)
  refine ⟨w, hD₁, hD₂, hf₁, hf₂, ?_⟩
  let β : Ω := Divisor.evalFun f E / Divisor.evalFun g D
  let χ : rootsOfUnity n K := Additive.toMul (α := rootsOfUnity n K)
    ((h1Character A ξ (hP).extClass
      (FiniteEtale.fundamentalGroupHom j η
        (FiniteEtale.fieldAutomorphismFiberAction X.functionField Ω σ))).toAdd)
  have hroot := congrArg Units.val
    (h1Character_genericKummerDivisor_fieldAutomorphism_root c hn hnK d b hb Ω σ q)
  change ι ((χ : Kˣ) : K) * (r q : Ω) = σ (r q : Ω) at hroot
  rw [hq, map_mul, genericStructuralScalar_fixed c Ω σ] at hroot
  have hs : ι (s : K) ≠ 0 := (map_ne_zero ι).mpr (Units.ne_zero s)
  have hχ : ι ((χ : Kˣ) : K) * β = σ β :=
    mul_right_cancel₀ hs ((mul_assoc _ _ _).trans hroot)
  have hβ : β ≠ 0 :=
    Units.ne_zero (Divisor.kummerEvaluationUnit n D E B f g hf hg hfdiv hgdiv hDE hDB)
  rw [hpair, hθbase]
  exact ((eq_div_iff hβ).mpr hχ).symm

end JacobianVarieties.WeilPairing
