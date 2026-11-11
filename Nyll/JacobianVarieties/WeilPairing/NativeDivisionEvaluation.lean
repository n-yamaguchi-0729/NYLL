/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.KummerEvaluationUnits
public import Nyll.AlgebraicCurves.Places.Degree.IsRationalAlgClosed
public import Nyll.EtaleCohomology.Classical.GenericUnitCohomology
public import Nyll.EtaleFundamentalGroups.Cohomology.ConstantGenericKummerDivisorExtension
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionMonodromy
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericKummerDivisorMonodromyRoots
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericKummerDivisorRootEquivalence
public import Nyll.EtaleFundamentalGroups.Cohomology.H1FiniteCover
public import Nyll.JacobianVarieties.WeilPairing.DivisionDifference
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Torsor.Basic

/-!
# Division evaluations in the original native Kummer fiber

Actual functions and division divisors produce a root by Weil
reciprocity. A specified actual normalization unit adjusts its power
to the specified original rational unit. The proved root equivalence
then constructs an actual point of that same native extension fiber.

For two division divisors of the same base divisor, displacement
between these actual points is the original divisorial Weil value.
The root, the fiber points, and the displacement comparison are all
constructed; no torsor or pairing identification is an input. There
is no restriction on the characteristic beyond the original Kummer
invertibility condition.
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
  (D E B : Divisor Ω F) (f g : F) (hf : f ≠ 0) (hg : g ≠ 0)
  (hfdiv : ∀ w : Place Ω F, w.ord f = (n : ℤ) * D w)
  (hgdiv : ∀ w : Place Ω F, w.ord g = (n : ℤ) * E w - B w)
  (hDE : ∀ w : Place Ω F, D w = 0 ∨ E w = 0)
  (hDB : ∀ w : Place Ω F, D w = 0 ∨ B w = 0)

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

variable (s : Ωˣ)

/-- The explicit division evaluation, with its normalized power equation,
as a root before passing to the monodromy fibre. -/
def nativeDivisionEvaluationRoot
    (hvalue : Divisor.evalFun f B * (s : Ω) ^ n = (a : Ω)) : { β : Ωˣ // β ^ n = a } := by
  let u : Ωˣ := Divisor.kummerEvaluationUnit n D E B f g hf hg hfdiv hgdiv hDE hDB
  have hu : (u : Ω) ^ n = Divisor.evalFun f B :=
    Divisor.kummerEvaluationUnit_pow n D E B f g hf hg hfdiv hgdiv hDE hDB
  refine ⟨u * s, ?_⟩
  apply Units.ext
  change ((u : Ω) * (s : Ω)) ^ n = (a : Ω)
  calc
    ((u : Ω) * (s : Ω)) ^ n = (u : Ω) ^ n * (s : Ω) ^ n := mul_pow _ _ _
    _ = Divisor.evalFun f B * (s : Ω) ^ n :=
      congrArg (fun z : Ω => z * (s : Ω) ^ n) hu
    _ = (a : Ω) := hvalue

/-- The actual point of the original native extension fiber whose
universal root is the explicit division-divisor evaluation. -/
def nativeDivisionEvaluationPoint
    (hvalue : Divisor.evalFun f B * (s : Ω) ^ n = (a : Ω)) :
    (extensionMonodromy A (P).f (P).g (P).zero hP (integerUnitSection X) ξ).obj.V :=
  (genericKummerDivisorRootFiberEquiv c hn hnK d b hb Ω).symm
    (nativeDivisionEvaluationRoot (n := n) (b := b) (Ω := Ω) (D := D) (E := E) (B := B)
      (f := f) (g := g) (hf := hf) (hg := hg) (hfdiv := hfdiv) (hgdiv := hgdiv)
      (hDE := hDE) (hDB := hDB) (s := s) (hvalue := hvalue))

/-- The original universal root takes exactly its required value
at the constructed original fiber point. -/
theorem nativeDivisionEvaluationPoint_root
    (hvalue : Divisor.evalFun f B * (s : Ω) ^ n = (a : Ω)) :
    r (nativeDivisionEvaluationPoint c hn hnK d b hb Ω D E B f g
      hf hg hfdiv hgdiv hDE hDB s hvalue) =
        Divisor.kummerEvaluationUnit n D E B f g hf hg hfdiv hgdiv hDE hDB * s :=
  genericKummerDivisorRootFiberEquiv_symm_root c hn hnK d b hb Ω
    (nativeDivisionEvaluationRoot (n := n) (b := b) (Ω := Ω) (D := D) (E := E) (B := B)
      (f := f) (g := g) (hf := hf) (hg := hg) (hfdiv := hfdiv) (hgdiv := hgdiv)
      (hDE := hDE) (hDB := hDB) (s := s) (hvalue := hvalue))

/-- The actual native displacement of two explicit division
evaluations is the actual Weil pairing of their division difference. -/
theorem nativeDivisionEvaluationPoint_displacement
    (hvalue : Divisor.evalFun f B * (s : Ω) ^ n = (a : Ω))
    (E' : Divisor Ω F) (g' : F) (hg' : g' ≠ 0)
    (hg'div : ∀ w : Place Ω F, w.ord g' = (n : ℤ) * E' w - B w)
    (hDE' : ∀ w : Place Ω F, D w = 0 ∨ E' w = 0) :
    let _ := extensionMonodromyTorsor A (P).f (P).g (P).zero hP (integerUnitSection X) ξ
    let q₀ := nativeDivisionEvaluationPoint c hn hnK d b hb Ω D E B f g
      hf hg hfdiv hgdiv hDE hDB s hvalue
    let q₁ := nativeDivisionEvaluationPoint c hn hnK d b hb Ω D E' B f g'
      hf hg' hfdiv hg'div hDE' hDB s hvalue
    ι (((rootsOfUnity n K).subtype
      (Additive.toMul (α := rootsOfUnity n K) (q₁ /ₛ q₀ : Multiplicative A).toAdd) : Kˣ) : K) =
      (WeilDatum.divisionDifference n D E E' B f g g' hf hg hg' hfdiv hgdiv hg'div
        hDE hDE' (fun w _ => w.isRational_of_isAlgClosed)
          (fun w _ => w.isRational_of_isAlgClosed)
          (fun w _ => w.isRational_of_isAlgClosed)).pairing := by
  intro coefficientTorsor q₀ q₁
  have h₀ : r q₀ =
      Divisor.kummerEvaluationUnit n D E B f g hf hg hfdiv hgdiv hDE hDB * s :=
    nativeDivisionEvaluationPoint_root c hn hnK d b hb Ω D E B f g
      hf hg hfdiv hgdiv hDE hDB s hvalue
  have h₁ : r q₁ =
      Divisor.kummerEvaluationUnit n D E' B f g' hf hg' hfdiv hg'div hDE' hDB * s :=
    nativeDivisionEvaluationPoint_root c hn hnK d b hb Ω D E' B f g'
      hf hg' hfdiv hg'div hDE' hDB s hvalue
  have hu := genericKummerDivisorMonodromyRoot_displacement c hn hnK d b hb Ω q₀ q₁
  rw [h₁, h₀, mul_div_mul_right_eq_div] at hu
  have h := congrArg Units.val hu
  simp only [Units.coe_map, Units.val_div_eq_div_val,
    Divisor.kummerEvaluationUnit_val] at h
  exact h.trans
    (WeilDatum.pairing_divisionDifference n D E E' B f g g' hf hg hg' hfdiv hgdiv hg'div
      hDE hDE' hDB (fun w _ => w.isRational_of_isAlgClosed)
      (fun w _ => w.isRational_of_isAlgClosed) (fun w _ => w.isRational_of_isAlgClosed)).symm

end JacobianVarieties.WeilPairing
