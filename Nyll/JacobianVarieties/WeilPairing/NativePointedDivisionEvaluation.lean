/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.Evaluation
public import Nyll.AlgebraicCurves.Divisors.KummerEvaluationUnits
public import Nyll.AlgebraicCurves.Places.Degree.IsRationalAlgClosed
public import Nyll.EtaleCohomology.Classical.GenericUnitCohomology
public import Nyll.EtaleFundamentalGroups.Cohomology.ConstantGenericKummerDivisorExtension
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionMonodromy
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericKummerDivisorMonodromyRoots
public import Nyll.EtaleFundamentalGroups.Cohomology.H1FiniteCover
public import Nyll.JacobianVarieties.WeilPairing.DivisionDifference
public import Nyll.JacobianVarieties.WeilPairing.NativeDivisionEvaluation
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Torsor.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Actual pointed evaluation roots and native Weil displacement

The actual point-evaluation formulas at the generic point and the
basepoint supply the native root equation after normalization. The
normalizing constant has an actual root in the algebraically closed
ground field. Multiplying both evaluation roots by its structural
image produces actual points of the same original native fiber.
Their original displacement is the original divisorial Weil value;
the common normalization cancels. No characteristic-zero comparison
of Jacobian covers is used.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory Limits AlgebraicCurve
open EtaleCohomology EtaleFundamentalGroups.Cohomology

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
local notation "ξ" => Spec.algebraMap X.functionField Ω ≫ j
local notation "A" => AddCommGrpCat.of (Additive (rootsOfUnity n K))
local notation "P" => constantGenericKummerDivisorExtension c hn hnK d b hb
local notation "hP" => constantGenericKummerDivisorExtension_shortExact c hn hnK d b hb
local notation "r" => genericKummerDivisorMonodromyRoot c hn hnK d b hb Ω
local notation "ι" =>
  CommRingCat.Hom.hom
    (Iso.inv (Scheme.ΓSpecIso (CommRingCat.of K)) ≫ Scheme.Hom.appTop (ξ ≫ c) ≫
      Iso.hom (Scheme.ΓSpecIso (CommRingCat.of Ω)))
local notation "a" => Units.map (RingHom.toMonoidHom (algebraMap X.functionField Ω))
  (Additive.toMul (genericPointUnitsH0Equiv X b))

/-- The actual two pointed division evaluations give actual points
of the original native Kummer fiber and the actual Weil displacement.
The only point-value inputs are the original generic evaluation and
the original nonzero basepoint value. -/
theorem exists_nativePointedDivisionEvaluation
    (D E E' : Divisor Ω F) (x ε : Place Ω F) (f g g' : F)
    (hf : f ≠ 0) (hg : g ≠ 0) (hg' : g' ≠ 0)
    (hfdiv : ∀ w : Place Ω F, w.ord f = (n : ℤ) * D w)
    (hgdiv : ∀ w : Place Ω F, w.ord g = (n : ℤ) * E w -
      (Finsupp.single x 1 + Finsupp.single ε (-1) : Divisor Ω F) w)
    (hg'div : ∀ w : Place Ω F, w.ord g' = (n : ℤ) * E' w -
      (Finsupp.single x 1 + Finsupp.single ε (-1) : Divisor Ω F) w)
    (hDE : ∀ w : Place Ω F, D w = 0 ∨ E w = 0)
    (hDE' : ∀ w : Place Ω F, D w = 0 ∨ E' w = 0)
    (hDx : D x = 0) (hDε : D ε = 0)
    (a₀ : Kˣ) (hx : x.evalAt f = (a : Ω)) (hε : ε.evalAt f = ι (a₀ : K)) :
    let coefficientAction :=
      extensionMonodromy (X := X) A
        (E := CategoryTheory.ShortComplex.X₂ P) («Q» := CategoryTheory.ShortComplex.X₃ P)
        (P).f (P).g (P).zero hP (integerUnitSection X) ξ
    let coefficientFiber : Type u := coefficientAction.obj.V
    let root : coefficientFiber → Ωˣ := r
    let coefficientTorsor :=
      extensionMonodromyTorsor (X := X) A
        (E := CategoryTheory.ShortComplex.X₂ P) («Q» := CategoryTheory.ShortComplex.X₃ P)
        (P).f (P).g (P).zero hP (integerUnitSection X) ξ
    ∃ s : Kˣ, s ^ n = a₀ ∧ ∃ q₀ q₁ : coefficientFiber,
      (root q₀ : Ω) = (Divisor.evalFun f E / Divisor.evalFun g D) * ι (s : K) ∧
      (root q₁ : Ω) = (Divisor.evalFun f E' / Divisor.evalFun g' D) * ι (s : K) ∧
      ι (((rootsOfUnity n K).subtype
        (Additive.toMul (α := rootsOfUnity n K)
          ((@SDiv.sdiv (Multiplicative A) coefficientFiber
            coefficientTorsor.toSDiv q₁ q₀).toAdd)) : Kˣ) : K) =
        (WeilDatum.divisionDifference n D E E'
          (Finsupp.single x 1 + Finsupp.single ε (-1)) f g g' hf hg hg'
            hfdiv hgdiv hg'div hDE hDE' (fun w _ => w.isRational_of_isAlgClosed)
          (fun w _ => w.isRational_of_isAlgClosed)
          (fun w _ => w.isRational_of_isAlgClosed)).pairing := by
  intro coefficientAction coefficientFiber root coefficientTorsor
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
  obtain ⟨s₀, hs₀⟩ := IsAlgClosed.exists_pow_nat_eq (a₀ : K) hn
  have hs₀ne : s₀ ≠ 0 := by
    intro h
    exact Units.ne_zero a₀
      (hs₀.symm.trans ((congrArg (fun z : K => z ^ n) h).trans
        (zero_pow (Nat.ne_of_gt hn))))
  let s : Kˣ := Units.mk0 s₀ hs₀ne
  have hs : s ^ n = a₀ := Units.ext hs₀
  let t : Ωˣ := Units.map (ι).toMonoidHom s
  have ht : (t : Ω) ^ n = ι (a₀ : K) :=
    congrArg Units.val
      (((map_pow (Units.map (ι).toMonoidHom) s n).symm).trans
        (congrArg (Units.map (ι).toMonoidHom) hs))
  have hx0 : x.evalAt f ≠ 0 := by rw [hx]; exact Units.ne_zero a
  have hε0 : ε.evalAt f ≠ 0 := by
    rw [hε]
    exact (map_ne_zero ι).mpr (Units.ne_zero a₀)
  have hvalue : Divisor.evalFun f B * (t : Ω) ^ n = (a : Ω) := by
    change Divisor.evalFun f (Finsupp.single x 1 + Finsupp.single ε (-1)) *
      (t : Ω) ^ n = (a : Ω)
    rw [Divisor.evalFun_single_sub_single f hx0 hε0, hx, hε, ht]
    exact div_mul_cancel₀ _ ((map_ne_zero ι).mpr (Units.ne_zero a₀))
  let q₀ := nativeDivisionEvaluationPoint c hn hnK d b hb Ω D E B f g
    hf hg hfdiv hgdiv hDE hDB t hvalue
  let q₁ := nativeDivisionEvaluationPoint c hn hnK d b hb Ω D E' B f g'
    hf hg' hfdiv hg'div hDE' hDB t hvalue
  refine ⟨s, hs, q₀, q₁, ?_, ?_, ?_⟩
  · have heval := congrArg Units.val
      (nativeDivisionEvaluationPoint_root c hn hnK d b hb Ω D E B f g
        hf hg hfdiv hgdiv hDE hDB t hvalue)
    exact heval.trans ((Units.val_mul _ _).trans
      (congrArg₂ (fun x y : Ω => x * y)
        (Divisor.kummerEvaluationUnit_val n D E B f g hf hg hfdiv hgdiv hDE hDB)
        (Units.coe_map (ι).toMonoidHom s)))
  · have heval := congrArg Units.val
      (nativeDivisionEvaluationPoint_root c hn hnK d b hb Ω D E' B f g'
        hf hg' hfdiv hg'div hDE' hDB t hvalue)
    exact heval.trans ((Units.val_mul _ _).trans
      (congrArg₂ (fun x y : Ω => x * y)
        (Divisor.kummerEvaluationUnit_val n D E' B f g' hf hg' hfdiv hg'div hDE' hDB)
        (Units.coe_map (ι).toMonoidHom s)))
  · exact nativeDivisionEvaluationPoint_displacement c hn hnK d b hb Ω D E B f g
      hf hg hfdiv hgdiv hDE hDB t hvalue E' g' hg' hg'div hDE'

end JacobianVarieties.WeilPairing
