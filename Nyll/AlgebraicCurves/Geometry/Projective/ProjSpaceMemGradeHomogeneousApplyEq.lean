/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Geometry.Projective.HomogeneousChartSections
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Choose
public import Lean.Elab.Tactic.NormCast
public import Nyll.SchemeTheory.ProjectiveSpace.Basic
public import Nyll.SchemeTheory.ProjectiveSpace.Cover
public import Nyll.AlgebraicCurves.Geometry.Projective.ProjTwistDatum
public import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule
public import Nyll.AlgebraicCurves.Geometry.Projective.ProjSpaceLinearMapHomogeneousSubmoduleTwistObjTopValEq
public import Nyll.AlgebraicCurves.Geometry.Projective.ProjSpaceIsFGHomInjectiveSaturatedTwistGradedModule
public import Nyll.AlgebraicCurves.Cohomology.Cech.ProjectiveSpace.GradedModuleHomHMapBijective
public import Nyll.AlgebraicCurves.Cohomology.Cech.ProjectiveSpace.GradedModuleHZeroShiftEqSecMk
public import Nyll.AlgebraicCurves.Geometry.Projective.ProjSpaceHomogeneousXMulPowApplyEq
public import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwist

/-!
# Proj Space exists forall mem grade exists is Homogeneous forall apply eq of is Closed
Immersion
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Projective.Proofs.ProjSpaceHomogeneousGradeLift

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

open HomogeneousLocalization

noncomputable section

namespace PolySurjBody

theorem map_appTop_π_eq_awayToSection_algebraMap (k : Type u) [CommRing k] (n : ℕ) (i : Fin (n +
  1)) (r : k) :
    (Proj (homogeneousSubmodule (Fin (n + 1)) k)).presheaf.map
        (homOfLE (le_top : Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) k) (X i) ≤ ⊤)).op
        ((ProjSpace.π k n).appTop ((Scheme.ΓSpecIso (.of k)).inv r))
      = Proj.awayToSection (homogeneousSubmodule (Fin (n + 1)) k) (X i)
          (algebraMap k (Away (homogeneousSubmodule (Fin (n + 1)) k) (X i)) r) :=
  ProjSpace.HomogeneousChartSections.map_appTop_π_eq_awayToSection_algebraMap k n i r

section Frac

variable {k : Type u} [CommRing k] {n : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

/-- The homogeneous fraction with the given numerator and a matching power of the chosen
coordinate. -/
noncomputable def frac (d : ℕ) (p : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) (i :
  Fin (n + 1)) : Away 𝒜 (X i) :=
  ProjSpace.HomogeneousChartSections.frac d p i

theorem val_frac (d : ℕ) (p : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) (i : Fin (n +
  1)) :
    (frac d p i).val = Localization.mk p.1 (⟨MvPolynomial.X i ^ d, ⟨d, rfl⟩⟩ : Submonoid.powers
      (MvPolynomial.X i)) :=
  ProjSpace.HomogeneousChartSections.val_frac d p i

theorem frac_add (d : ℕ) (p q : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) (i : Fin (n
  + 1)) :
    frac d (p + q) i = frac d p i + frac d q i :=
  ProjSpace.HomogeneousChartSections.frac_add d p q i

theorem frac_smul (d : ℕ) (c : k) (p : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) (i :
  Fin (n + 1)) :
    frac d (c • p) i = algebraMap k (Away 𝒜 (X i)) c * frac d p i :=
  ProjSpace.HomogeneousChartSections.frac_smul d c p i

theorem awayMap_frac_eq (d : ℕ) (p : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) (i j :
  Fin (n + 1)) :
    awayMap 𝒜 (ProjSpace.X_mem_one k n j) rfl (frac d p i)
      = awayMap 𝒜 (ProjSpace.X_mem_one k n j) rfl (ProjSpace.ratio k n i j) ^ d
          * awayMap 𝒜 (ProjSpace.X_mem_one k n i)
              (mul_comm (X i) (X j) : (X i * X j : MvPolynomial (Fin (n + 1)) k) = X j * X i) (frac
                d p j) :=
  ProjSpace.HomogeneousChartSections.awayMap_frac_eq d p i j

end Frac

section Comp

variable {k : Type u} [CommRing k] {n : ℕ} {Z : Scheme.{u}}
  (φ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

/-- The section on a pulled-back projective chart induced by a homogeneous localization element. -/
noncomputable def pullAway (i : Fin (n + 1)) (a : Away 𝒜 (X i)) : Γ(Z, ProjSpace.pullbackChart φ i)
  :=
  ProjSpace.HomogeneousChartSections.pullAway φ i a

theorem pullAway_eq (i : Fin (n + 1)) (a : Away 𝒜 (X i)) :
    pullAway φ i a = (φ.app (Proj.basicOpen 𝒜 (X i))) (Proj.awayToSection 𝒜 (X i) a) :=
  ProjSpace.HomogeneousChartSections.pullAway_eq φ i a

theorem pullAway_add (i : Fin (n + 1)) (a b : Away 𝒜 (X i)) :
    pullAway φ i (a + b) = pullAway φ i a + pullAway φ i b :=
  ProjSpace.HomogeneousChartSections.pullAway_add φ i a b

theorem pullAway_mul (i : Fin (n + 1)) (a b : Away 𝒜 (X i)) :
    pullAway φ i (a * b) = pullAway φ i a * pullAway φ i b :=
  ProjSpace.HomogeneousChartSections.pullAway_mul φ i a b

theorem pullAway_zero (i : Fin (n + 1)) : pullAway φ i 0 = 0 :=
  ProjSpace.HomogeneousChartSections.pullAway_zero φ i

theorem restrictFun_pullAway_left (i j : Fin (n + 1)) (a : Away 𝒜 (X i)) :
    ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left φ i j) (pullAway φ i a)
      = (φ.app (Proj.basicOpen 𝒜 (X i * X j))).hom
          ((Proj.awayToSection 𝒜 (X i * X j)).hom (awayMap 𝒜 (ProjSpace.X_mem_one k n j) rfl a)) :=
  ProjSpace.HomogeneousChartSections.restrictFun_pullAway_left φ i j a

theorem restrictFun_pullAway_right (i j : Fin (n + 1)) (a : Away 𝒜 (X j)) :
    ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_right φ i j) (pullAway φ j a)
      = (φ.app (Proj.basicOpen 𝒜 (X i * X j))).hom
          ((Proj.awayToSection 𝒜 (X i * X j)).hom (awayMap 𝒜 (ProjSpace.X_mem_one k n i)
            (mul_comm (X i) (X j) : (X i * X j : MvPolynomial (Fin (n + 1)) k) = X j * X i) a)) :=
  ProjSpace.HomogeneousChartSections.restrictFun_pullAway_right φ i j a

theorem restrictFun_pullAway_frac (d : ℕ) (p : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k
  d)) (i j : Fin (n + 1)) :
    ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left φ i j) (pullAway φ i (frac d p i))
      = ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left φ i j) (ProjSpace.frameUnit φ i j)
        ^ d
          * ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_right φ i j) (pullAway φ j (frac d
            p j)) :=
  ProjSpace.HomogeneousChartSections.restrictFun_pullAway_frac φ d p i j

theorem pullAway_algebraMap (i : Fin (n + 1)) (c : k) {W : Z.Opens} (hW : W ≤
  ProjSpace.pullbackChart φ i) :
    ProjSpace.restrictFun hW (pullAway φ i (algebraMap k (Away 𝒜 (X i)) c))
      = (Scheme.TwoAffineOpenCover.algebraOfHom (φ ≫ ProjSpace.π k n) W).algebraMap c :=
  ProjSpace.HomogeneousChartSections.pullAway_algebraMap φ i c hW

end Comp

section Main

variable {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
  (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

theorem frameUnit_eq_pullAway (i j : Fin (n + 1)) :
    ProjSpace.frameUnit ι i j = pullAway ι i (ProjSpace.ratio A n i j) :=
  ProjSpace.HomogeneousChartSections.frameUnit_eq_pullAway ι i j

theorem xMul_pow_apply (j : Fin (n + 1)) (k : ℕ) (f : ProjSpace.twistFam (ι ≫ ProjSpace.π A n) ι)
  (d : ℤ) (i : Fin (n + 1)) :
    (((ProjSpace.twistGradedModule ι (ι ≫ ProjSpace.π A n)).xMul j ^ k) f) d i =
      ProjSpace.restrictFun (inf_le_right : (⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart ι i ≤
        ProjSpace.pullbackChart ι i)
        (ProjSpace.frameUnit ι i j) ^ k * f (d - k) i :=
  ProjSpace.HomogeneousChartSections.xMul_pow_apply ι j k f d i

theorem exists_eq_pullAway_mk [IsClosedImmersion ι] (j : Fin (n + 1)) (z : Γ(Z,
  ProjSpace.pullbackChart ι j)) :
    ∃ (a : ℕ) (G : MvPolynomial (Fin (n + 1)) A) (hG : G ∈ 𝒜 a),
      z = pullAway ι j (Away.mk 𝒜 (ProjSpace.X_mem_one A n j) a G (by simpa using hG)) :=
  ProjSpace.HomogeneousChartSections.exists_eq_pullAway_mk ι j z

theorem basicOpen_frameUnit_le (i j : Fin (n + 1)) :
    Z.basicOpen (ProjSpace.frameUnit ι i j) ≤ ProjSpace.pullbackChart ι j :=
  ProjSpace.HomogeneousChartSections.basicOpen_frameUnit_le ι i j

theorem exists_pow_mul_eq_zero [IsClosedImmersion ι] (i j : Fin (n + 1)) (δ : Γ(Z,
  ProjSpace.pullbackChart ι i))
    (hδ : ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left ι i j) δ = 0) :
    ∃ N : ℕ, ProjSpace.frameUnit ι i j ^ N * δ = 0 :=
  ProjSpace.HomogeneousChartSections.exists_pow_mul_eq_zero ι i j δ hδ

theorem pullAway_pow (i : Fin (n + 1)) (a : Away 𝒜 (X i)) (N : ℕ) :
    pullAway ι i (a ^ N) = pullAway ι i a ^ N :=
  ProjSpace.HomogeneousChartSections.pullAway_pow ι i a N

theorem frac_congr {d₁ d₂ : ℕ} (h : d₁ = d₂) (p : ↥(𝒜 d₁)) (i : Fin (n + 1)) :
    frac d₁ p i = frac d₂ ⟨p.1, h ▸ p.2⟩ i :=
  ProjSpace.HomogeneousChartSections.frac_congr h p i

theorem frameUnit_pow_mul_pullAway_frac (i j : Fin (n + 1)) (N d : ℕ) (p : ↥(𝒜 d)) :
    ProjSpace.frameUnit ι i j ^ N * pullAway ι i (frac d p i) =
      pullAway ι i (frac (d + N) ⟨X j ^ N * p.1, by
        have h := SetLike.mul_mem_graded (SetLike.pow_mem_graded N (ProjSpace.X_mem_one A n j)) p.2
        rwa [smul_eq_mul, mul_one, Nat.add_comm N d] at h⟩ i) :=
  ProjSpace.HomogeneousChartSections.frameUnit_pow_mul_pullAway_frac ι i j N d p

end Main

section Units

variable {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
  (φ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A
local notation "MM" => ProjSpace.twistGradedModule φ (φ ≫ ProjSpace.π A n)

/-- The compatible twist family induced by a homogeneous section of degree `d`. -/
def unitFam (d : ℕ) (p : ↥(𝒜 d)) : ProjSpace.twistFam (φ ≫ ProjSpace.π A n) φ :=
  ProjSpace.objToTwistFam φ (φ ≫ ProjSpace.π A n) d
    ((AlgebraicGeometry.ProjSpace.exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq φ
    d).choose p)

theorem unitFam_mem (d : ℕ) (p : ↥(𝒜 d)) : unitFam φ d p ∈ (MM).grade (d : ℤ) :=
  ProjSpace.objToTwistFam_mem φ (φ ≫ ProjSpace.π A n) d _

theorem unitFam_apply_self (d : ℕ) (p : ↥(𝒜 d)) (i : Fin (n + 1)) :
    unitFam φ d p (d : ℤ) i = ProjSpace.restrictFun (inf_le_right : (⊤ : Z.Opens) ⊓
      ProjSpace.pullbackChart φ i ≤ ProjSpace.pullbackChart φ i)
      (pullAway φ i (frac d p i)) := by
  have h := (AlgebraicGeometry.ProjSpace.exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq
    φ d).choose_spec.1 p.1 ((MvPolynomial.mem_homogeneousSubmodule d p.1).mp p.2) i
  simp only [unitFam, ProjSpace.objToTwistFam, ite_eq_left]
  exact h

theorem unitFam_apply_ne (d : ℕ) (p : ↥(𝒜 d)) (d' : ℤ) (hd : d' ≠ d) (i : Fin (n + 1)) :
    unitFam φ d p d' i = 0 := by
  simp only [unitFam, ProjSpace.objToTwistFam, ite_eq_right hd]
  rfl

theorem unitFam_add (d : ℕ) (p q : ↥(𝒜 d)) : unitFam φ d (p + q) = unitFam φ d p + unitFam φ d q :=
  by
  funext d' i
  by_cases hd : d' = d
  · subst hd
    change _ = unitFam φ d p (d : ℤ) i + unitFam φ d q (d : ℤ) i
    rw [unitFam_apply_self, unitFam_apply_self, unitFam_apply_self, frac_add, pullAway_add, map_add]
  · change _ = unitFam φ d p d' i + unitFam φ d q d' i
    rw [unitFam_apply_ne φ d _ d' hd, unitFam_apply_ne φ d _ d' hd, unitFam_apply_ne φ d _ d' hd,
      add_zero]

theorem unitFam_smul (d : ℕ) (c : A) (p : ↥(𝒜 d)) : unitFam φ d (c • p) = c • unitFam φ d p := by
  funext d' i
  by_cases hd : d' = d
  · subst hd
    rw [ProjSpace.twistFam.smul_apply, unitFam_apply_self, unitFam_apply_self, frac_smul,
      pullAway_mul, map_mul,
      pullAway_algebraMap]
  · rw [ProjSpace.twistFam.smul_apply, unitFam_apply_ne φ d _ d' hd, unitFam_apply_ne φ d _ d' hd,
      mul_zero]

theorem xMul_unitFam (j : Fin (n + 1)) (d : ℕ) (p : ↥(𝒜 d)) :
    (MM).xMul j (unitFam φ d p) = unitFam φ (d + 1) ⟨X j * p.1, by
      have h := SetLike.mul_mem_graded (ProjSpace.X_mem_one A n j) p.2
      rwa [Nat.add_comm 1 d] at h⟩ := by
  funext d' i
  change ProjSpace.restrictFun (inf_le_right : (⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart φ i ≤
    ProjSpace.pullbackChart φ i)
      (ProjSpace.frameUnit φ i j) * unitFam φ d p (d' - 1) i = _
  by_cases hd : d' = (d + 1 : ℕ)
  · subst hd
    have h1 : ((d + 1 : ℕ) : ℤ) - 1 = (d : ℤ) := by push_cast; ring
    rw [h1, unitFam_apply_self, unitFam_apply_self, ← map_mul, ← pow_one (ProjSpace.frameUnit φ i
      j),
      frameUnit_pow_mul_pullAway_frac]
    congr 3
    apply Subtype.ext
    simp only [pow_one]
  · rw [unitFam_apply_ne φ (d + 1) _ d' hd, unitFam_apply_ne φ d _ (d' - 1)
      (by intro h; apply hd; omega), mul_zero]

end Units

section UnitsMon

variable {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
  (φ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A
local notation "MM" => ProjSpace.twistGradedModule φ (φ ≫ ProjSpace.π A n)

theorem prod_X_pow_mul_mem (a : Fin (n + 1) → ℕ) (d : ℕ) (p : ↥(𝒜 d)) :
    (∏ j, X j ^ a j) * p.1 ∈ (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (d + ∑ j, a j) :=
      by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  have h := (ProjSpaceCech.GradedModule.isHomogeneous_prod_X_pow (R := A) a).mul
    ((MvPolynomial.mem_homogeneousSubmodule d p.1).mp p.2)
  rwa [Nat.add_comm (∑ j, a j) d] at h

theorem unitFam_congr {d₁ d₂ : ℕ} (h : d₁ = d₂) (p : ↥(𝒜 d₁)) (q : ↥(𝒜 d₂)) (hpq : p.1 = q.1) :
    unitFam φ d₁ p = unitFam φ d₂ q := by
  subst h
  obtain rfl : p = q := Subtype.ext hpq
  rfl

theorem monMul_unitFam (a : Fin (n + 1) → ℕ) (d : ℕ) (p : ↥(𝒜 d)) :
    ProjSpaceCech.GradedModule.monMul (MM) a (unitFam φ d p) =
      unitFam φ (d + ∑ j, a j) ⟨(∏ j, X j ^ a j) * p.1, prod_X_pow_mul_mem a d p⟩ := by
  suffices H : ∀ (N : ℕ) (a : Fin (n + 1) → ℕ), ∑ j, a j = N → ∀ (d : ℕ) (p : ↥(𝒜 d)),
      ProjSpaceCech.GradedModule.monMul (MM) a (unitFam φ d p) =
        unitFam φ (d + ∑ j, a j) ⟨(∏ j, X j ^ a j) * p.1, prod_X_pow_mul_mem a d p⟩ from H _ a rfl
          d p
  intro N
  induction N with
  | zero =>
    intro a ha d p
    have ha0 : a = 0 := by
      funext j
      have := Finset.sum_eq_zero_iff.mp ha j (Finset.mem_univ j)
      simpa using this
    subst ha0
    erw [ProjSpaceCech.GradedModule.monMul_zero, LinearMap.id_apply]
    exact unitFam_congr φ
      (by simp only [Pi.zero_apply, Finset.sum_const_zero, add_zero]) _ _
      (by simp only [Pi.zero_apply, pow_zero, Finset.prod_const_one, one_mul])
  | succ N ih =>
    intro a ha d p
    obtain ⟨j, hj⟩ : ∃ j, 0 < a j := by
      by_contra h
      push Not at h
      have : ∑ j, a j = 0 := Finset.sum_eq_zero fun j _ => Nat.le_zero.mp (h j)
      omega
    set a' : Fin (n + 1) → ℕ := a - Pi.single j 1 with ha'
    have haa : a = a' + Pi.single j 1 := by
      funext l
      by_cases hl : l = j
      · subst hl; simp only [Pi.add_apply, ha', Pi.sub_apply, Pi.single_eq_same]; omega
      · simp only [Pi.add_apply, ha', Pi.sub_apply, Pi.single_eq_of_ne hl,
          Nat.sub_zero, add_zero]
    have hsum : ∑ l, a' l = N := by
      have h1 : ∑ l, a l = ∑ l, a' l + ∑ l, (Pi.single j 1 : Fin (n + 1) → ℕ) l := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun l _ => by rw [haa]; rfl
      rw [Finset.sum_pi_single' j 1, ite_eq_left (Finset.mem_univ j)] at h1
      omega
    erw [haa, ProjSpaceCech.GradedModule.monMul_add_apply,
      ProjSpaceCech.GradedModule.monMul_single, pow_one,
      xMul_unitFam, ih a' hsum]
    refine unitFam_congr φ (by rw [← haa, ha, hsum]; omega) _ _ ?_
    simp only
    have hprod : (∏ l, (X l : MvPolynomial (Fin (n + 1)) A) ^ (a' + Pi.single j 1 : Fin (n + 1) →
      ℕ) l) =
        (∏ l, X l ^ a' l) * X j := by
      rw [show (∏ l, (X l : MvPolynomial (Fin (n + 1)) A) ^ (a' + Pi.single j 1 : Fin (n + 1) → ℕ)
        l) =
          ∏ l, (X l ^ a' l * X l ^ (Pi.single j 1 : Fin (n + 1) → ℕ) l) from
          Finset.prod_congr rfl fun l _ => by rw [Pi.add_apply, pow_add],
        Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_eq_single j (fun l _ hl => by rw [Pi.single_eq_of_ne hl, pow_zero])
        (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, pow_one]
    rw [hprod]
    ring

/--
The graded-module homomorphism inserting an element into the chosen component of a finite
product.
-/
def singleHom {ι' : Type} [Fintype ι'] [DecidableEq ι'] (D : ι' → ProjSpaceCech.GradedModule A n)
  (k : ι') :
    ProjSpaceCech.GradedModule.Hom (D k) (ProjSpaceCech.GradedModule.pi D) where
  toLinearMap := LinearMap.single A (fun k => (D k).M) k
  mem_grade d m hm := by
    intro k' _
    change (Pi.single k m : ∀ k, (D k).M) k' ∈ (D k').grade d
    by_cases hk : k = k'
    · subst hk
      rw [Pi.single_eq_same]; exact hm
    · rw [Pi.single_eq_of_ne (Ne.symm hk)]; exact zero_mem _
  xMul_comm j := by
    apply LinearMap.ext
    intro m
    funext k'
    change (Pi.single k ((D k).xMul j m) : ∀ k, (D k).M) k' =
      (D k').xMul j ((Pi.single k m : ∀ k, (D k).M) k')
    by_cases hk : k = k'
    · subst hk; rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne (Ne.symm hk), Pi.single_eq_of_ne (Ne.symm hk), map_zero]

theorem absorb (K : ℕ) {D' : ProjSpaceCech.GradedModule A n} (σ :
  ProjSpaceCech.GradedModule.Presentation D')
    [DecidableEq σ.J] (ψ : ProjSpaceCech.GradedModule.Hom D' (MM)) (e : σ.J → ℕ) (he : ∀ k, (e k :
      ℤ) = (K : ℤ) - σ.d₀ k)
    (hK : ∀ (k : σ.J) (j : Fin (n + 1)), ∃ (F : MvPolynomial (Fin (n + 1)) A) (hF : F ∈ 𝒜 (e k)),
      ((MM).xMul j ^ K) (ψ.toLinearMap (σ.hom.toLinearMap (Pi.single k (1 : MvPolynomial (Fin (n +
        1)) A)))) =
        unitFam φ (e k) ⟨F, hF⟩) :
    ∃ d₁ : ℤ, ∀ d : ℕ, d₁ ≤ (d : ℤ) → ∀ m' ∈ D'.grade (d : ℤ),
      ∃ (G : MvPolynomial (Fin (n + 1)) A) (hG : G ∈ 𝒜 d), ψ.toLinearMap m' = unitFam φ d ⟨G, hG⟩
        := by
  classical
  choose Fk hFk hk using hK
  let U : ∀ d : ℕ, ↥(𝒜 d) →ₗ[A] ProjSpace.twistFam (φ ≫ ProjSpace.π A n) φ := fun d =>
    { toFun := unitFam φ d, map_add' := unitFam_add φ d, map_smul' := unitFam_smul φ d }
  have hU : ∀ (d : ℕ) p, U d p = unitFam φ d p := fun _ _ => rfl
  refine ⟨(n + 1 : ℤ) * K + ∑ k, |σ.d₀ k|, ?_⟩
  intro d hd m' hm'
  suffices hsuff : ψ.toLinearMap m' ∈ LinearMap.range (U d) by
    obtain ⟨G, hG⟩ := hsuff
    exact ⟨G.1, G.2, hG.symm⟩
  obtain ⟨f, hf, rfl⟩ := σ.surj (d : ℤ) m' hm'
  have hfsum : f = ∑ k, (singleHom (fun k => ProjSpaceCech.GradedModule.FD A n (σ.d₀ k))
    k).toLinearMap (f k) := by
    funext k'
    change f k' =
      (∑ k, (Pi.single k (f k) : ∀ k, (ProjSpaceCech.GradedModule.FD A n (σ.d₀ k)).M)) k'
    rw [Finset.sum_apply, Finset.sum_eq_single k' (fun k _ hk => Pi.single_eq_of_ne (Ne.symm hk) _)
      (fun h => (h (Finset.mem_univ _)).elim), Pi.single_eq_same]
  rw [hfsum, map_sum, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  have hfk : f k ∈ ProjSpaceCech.GradedModule.freeGrade A n ((d : ℤ) + σ.d₀ k) := hf k
    (Set.mem_univ k)
  by_cases hneg : (d : ℤ) + σ.d₀ k < 0
  · have : f k = 0 := by
      simp only [ProjSpaceCech.GradedModule.freeGrade, not_le.mpr hneg, ite_false] at hfk
      exact hfk
    rw [this, map_zero, map_zero, map_zero]
    exact (LinearMap.range (U d)).zero_mem
  push Not at hneg
  rw [ProjSpaceCech.GradedModule.freeGrade_of_nonneg A n hneg] at hfk
  replace hfk : (f k : MvPolynomial (Fin (n + 1)) A).IsHomogeneous (((d : ℤ) + σ.d₀ k).toNat) :=
    (MvPolynomial.mem_homogeneousSubmodule _ _).mp hfk
  rw [MvPolynomial.as_sum (f k)]
  have hms : (singleHom (fun k => ProjSpaceCech.GradedModule.FD A n (σ.d₀ k)) k).toLinearMap
      (∑ v ∈ (f k).support, MvPolynomial.monomial v ((f k : MvPolynomial (Fin (n + 1)) A).coeff v))
      = ∑ v ∈ (f k).support, (singleHom (fun k => ProjSpaceCech.GradedModule.FD A n (σ.d₀ k))
        k).toLinearMap
          (MvPolynomial.monomial v ((f k : MvPolynomial (Fin (n + 1)) A).coeff v)) := map_sum _ _ _
  erw [hms]
  rw [map_sum, map_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  have hdegα : ∑ j, α j = ((d : ℤ) + σ.d₀ k).toNat := by
    have hw := hfk (MvPolynomial.mem_support_iff.mp hα)
    have hdw : Finsupp.degree α = Finsupp.weight (1 : Fin (n + 1) → ℕ) α := by
      rw [Finsupp.degree_eq_weight_one]; rfl
    rw [← Finsupp.degree_eq_sum, hdw]
    exact hw
  have hbig : (n + 1) * K ≤ ∑ j, α j := by
    have h1 : ((n + 1 : ℤ) * K) ≤ (d : ℤ) + σ.d₀ k := by
      have hle : |σ.d₀ k| ≤ ∑ k, |σ.d₀ k| :=
        Finset.single_le_sum (f := fun k => |σ.d₀ k|) (fun k _ => abs_nonneg _) (Finset.mem_univ k)
      have := neg_abs_le (σ.d₀ k)
      omega
    have h2 : (((d : ℤ) + σ.d₀ k).toNat : ℤ) = (d : ℤ) + σ.d₀ k := Int.toNat_of_nonneg hneg
    have h3 : ((n + 1 : ℤ) * K) ≤ ((∑ j, α j : ℕ) : ℤ) := by rw [hdegα, h2]; exact h1
    exact_mod_cast h3
  obtain ⟨j, hj⟩ : ∃ j, K ≤ α j := by
    by_contra hcon
    push Not at hcon
    have : ∑ j, α j < ∑ j : Fin (n + 1), K := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun j _ => hcon j)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
    omega
  have hmon : MvPolynomial.monomial α ((f k : MvPolynomial (Fin (n + 1)) A).coeff α)
      = (f k : MvPolynomial (Fin (n + 1)) A).coeff α • ProjSpaceCech.GradedModule.monMul
        (ProjSpaceCech.GradedModule.FD A n (σ.d₀ k))
          (fun j => α j) (1 : MvPolynomial (Fin (n + 1)) A) := by
    change _ = _ • ProjSpaceCech.GradedModule.monMul (ProjSpaceCech.GradedModule.free A n) (fun j =>
      α j) (1 : MvPolynomial (Fin (n + 1)) A)
    rw [ProjSpaceCech.GradedModule.free_monMul_apply]
    erw [mul_one]
    rw [MvPolynomial.monomial_eq, Finsupp.prod_pow]
    exact (MvPolynomial.smul_eq_C_mul _ _).symm
  rw [hmon, map_smul, map_smul, map_smul]
  refine Submodule.smul_mem _ _ ?_
  erw [ProjSpaceCech.GradedModule.Hom.map_monMul, ProjSpaceCech.GradedModule.Hom.map_monMul,
    ProjSpaceCech.GradedModule.Hom.map_monMul]
  have hsplit : (fun i => α i) = (fun i => α i - (Pi.single j K : Fin (n + 1) → ℕ) i) + (Pi.single
    j K : Fin (n + 1) → ℕ) := by
    funext i
    by_cases hi : i = j
    · subst hi; simp only [Pi.add_apply, Pi.single_eq_same]; omega
    · simp only [Pi.add_apply, Pi.single_eq_of_ne hi]; omega
  rw [hsplit, ProjSpaceCech.GradedModule.monMul_add_apply, ProjSpaceCech.GradedModule.monMul_single]
  change ProjSpaceCech.GradedModule.monMul (MM) (fun i => α i - (Pi.single j K : Fin (n + 1) → ℕ) i)
      (((MM).xMul j ^ K) (ψ.toLinearMap (σ.hom.toLinearMap (Pi.single k (1 : MvPolynomial (Fin (n +
        1)) A))))) ∈
      LinearMap.range (U d)
  rw [hk k j, monMul_unitFam]
  have hsumsub : ∑ i, (α i - (Pi.single j K : Fin (n + 1) → ℕ) i) = (∑ i, α i) - K := by
    have h1 : ∑ i, (α i - (Pi.single j K : Fin (n + 1) → ℕ) i) + ∑ i, (Pi.single j K : Fin (n + 1)
      → ℕ) i = ∑ i, α i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : i = j
      · subst hi; simp only [Pi.single_eq_same]; omega
      · simp only [Pi.single_eq_of_ne hi]; omega
    have h2 : ∑ i, (Pi.single j K : Fin (n + 1) → ℕ) i = K := by
      rw [Finset.sum_eq_single j (fun i _ hi => Pi.single_eq_of_ne hi _) (fun h => (h
        (Finset.mem_univ _)).elim),
        Pi.single_eq_same]
    omega
  have hdeg : e k + ∑ i, (α i - (Pi.single j K : Fin (n + 1) → ℕ) i) = d := by
    have h2 : (((d : ℤ) + σ.d₀ k).toNat : ℤ) = (d : ℤ) + σ.d₀ k := Int.toNat_of_nonneg hneg
    have hek := he k
    have hKle : K ≤ ((d : ℤ) + σ.d₀ k).toNat := by
      rw [← hdegα]; exact hj.trans (Finset.single_le_sum (fun i _ => Nat.zero_le (α i))
        (Finset.mem_univ j))
    rw [hsumsub, hdegα]
    zify [hKle]
    rw [h2] at *
    omega
  refine ⟨⟨(∏ i, X i ^ (α i - (Pi.single j K : Fin (n + 1) → ℕ) i)) * Fk k j, hdeg ▸
    prod_X_pow_mul_mem _ (e k) ⟨Fk k j, hFk k j⟩⟩, ?_⟩
  rw [hU]
  exact unitFam_congr φ hdeg.symm _ _ rfl

end UnitsMon

section Glob

variable {A : Type u} [CommRing A] {n : ℕ}

/-- The degree-zero Čech index consisting of the single coordinate `i`. -/
def vtx (i : Fin (n + 1)) : ProjSpaceCech.Idx n 0 :=
  ⟨fun _ => i, fun a b hab => absurd (Fin.lt_def.mp hab) (by have := a.2; have := b.2; omega)⟩

theorem img_vtx (i : Fin (n + 1)) : ProjSpaceCech.Idx.img n (vtx i) = {i} := by
  ext j
  simp [ProjSpaceCech.Idx.img, vtx, eq_comm]

variable (D : ProjSpaceCech.GradedModule A n)

/-- The localized section induced by a homogeneous element of degree zero. -/
def globSec (I : Finset (Fin (n + 1))) (x : D.M)
    (hx : x ∈ D.grade (∑ j : Fin (n + 1), (((0 : Fin (n + 1) → ℕ) j : ℕ) : ℤ))) :
    ProjSpaceCech.GradedModule.sec D I :=
  ProjSpaceCech.GradedModule.sec.mk D I ⟨0, fun _ _ => rfl, x, hx⟩

theorem secIncl_globSec {I J : Finset (Fin (n + 1))} (hIJ : I ⊆ J) (x : D.M)
    (hx : x ∈ D.grade (∑ j : Fin (n + 1), (((0 : Fin (n + 1) → ℕ) j : ℕ) : ℤ))) :
    ProjSpaceCech.GradedModule.secIncl D hIJ (globSec D I x hx) = globSec D J x hx := rfl

/--
The degree-zero cohomology class represented by the compatible localizations of a homogeneous
element of degree zero.
-/
def globCocycle (x : D.M) (hx : x ∈ D.grade (∑ j : Fin (n + 1), (((0 : Fin (n + 1) → ℕ) j : ℕ) :
  ℤ))) :
    ProjSpaceCech.GradedModule.H D 0 :=
  show ↥(LinearMap.ker (ProjSpaceCech.GradedModule.d D 0)) from
  ⟨fun s => globSec D (ProjSpaceCech.Idx.img n s) x hx, by
    rw [LinearMap.mem_ker]
    funext s
    rw [ProjSpaceCech.GradedModule.d_apply, Fin.sum_univ_two]
    change (-1 : A) ^ ((0 : Fin 2) : ℕ) • ProjSpaceCech.GradedModule.secIncl D _ (globSec D _ x hx)
      +
      (-1 : A) ^ ((1 : Fin 2) : ℕ) • ProjSpaceCech.GradedModule.secIncl D _ (globSec D _ x hx) = 0
    rw [secIncl_globSec, secIncl_globSec]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
      neg_one_smul, add_neg_cancel]⟩

theorem globCocycle_val (x : D.M) (hx : x ∈ D.grade (∑ j : Fin (n + 1), (((0 : Fin (n + 1) → ℕ) j :
  ℕ) : ℤ)))
    (s : ProjSpaceCech.Idx n 0) :
    (show ↥(LinearMap.ker (ProjSpaceCech.GradedModule.d D 0)) from globCocycle D x hx).1 s =
      globSec D (ProjSpaceCech.Idx.img n s) x hx := rfl

end Glob

section Extract

variable {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
  (φ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))

local notation "MM" => ProjSpace.twistGradedModule φ (φ ≫ ProjSpace.π A n)

theorem apply_eq_of_globSec_eq (d : ℕ) (x y : ProjSpace.twistFam (φ ≫ ProjSpace.π A n) φ)
    (hx : x ∈ ((MM).shift (d : ℤ)).grade (∑ j : Fin (n + 1), (((0 : Fin (n + 1) → ℕ) j : ℕ) : ℤ)))
    (hy : y ∈ ((MM).shift (d : ℤ)).grade (∑ j : Fin (n + 1), (((0 : Fin (n + 1) → ℕ) j : ℕ) : ℤ)))
    (i : Fin (n + 1))
    (h : globSec ((MM).shift (d : ℤ)) {i} x hx = globSec ((MM).shift (d : ℤ)) {i} y hy) :
    x (d : ℤ) i = y (d : ℤ) i := by
  obtain ⟨c, hc, heq⟩ := (ProjSpaceCech.GradedModule.sec_mk_eq _ _).mp h
  have hcs : c = Pi.single i (c i) := by
    funext j
    by_cases hj : j = i
    · subst hj; rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hj]
      exact hc j (by simpa using hj)
  change ProjSpaceCech.GradedModule.monMul (MM) (c + 0) x = ProjSpaceCech.GradedModule.monMul (MM)
    (c + 0) y at heq
  rw [add_zero, hcs, ProjSpaceCech.GradedModule.monMul_single] at heq
  have h2 := congrArg (fun f : ProjSpace.twistFam (φ ≫ ProjSpace.π A n) φ => f ((d : ℤ) + (c i :
    ℕ)) i) heq
  rw [xMul_pow_apply, xMul_pow_apply, ProjSpace.frameUnit_self, map_one, one_pow, one_mul, one_mul,
    add_sub_cancel_right] at h2
  exact h2

end Extract

section HomLemmas

variable {A : Type u} [CommRing A] {n : ℕ} {D₁ D₂ : ProjSpaceCech.GradedModule A n}

theorem secMap_mk (h : ProjSpaceCech.GradedModule.Hom D₁ D₂) (I : Finset (Fin (n + 1)))
    (x : ProjSpaceCech.GradedModule.Frac D₁ I) :
    ProjSpaceCech.GradedModule.Hom.secMap h I (ProjSpaceCech.GradedModule.sec.mk D₁ I x) =
      ProjSpaceCech.GradedModule.sec.mk D₂ I ⟨x.denExp, x.hden, h.toLinearMap x.num, h.mem_grade _
        _ x.hnum⟩ := rfl

theorem HMap_zero_val (h : ProjSpaceCech.GradedModule.Hom D₁ D₂) (c : ProjSpaceCech.GradedModule.H
  D₁ 0)
    (s : ProjSpaceCech.Idx n 0) :
    (show ↥(LinearMap.ker (ProjSpaceCech.GradedModule.d D₂ 0)) from
      ProjSpaceCech.GradedModule.Hom.HMap h 0 c).1 s =
      ProjSpaceCech.GradedModule.Hom.secMap h (ProjSpaceCech.Idx.img n s)
        ((show ↥(LinearMap.ker (ProjSpaceCech.GradedModule.d D₁ 0)) from c).1 s) := rfl

theorem sat_shift {M' M : ProjSpaceCech.GradedModule A n} (ψ : ProjSpaceCech.GradedModule.Hom M' M)
    (hsat : ∀ (j : Fin (n + 1)) (e : ℤ), ∀ x ∈ M.grade e,
      ∃ k : ℕ, ∃ x' ∈ M'.grade (e + k), ψ.toLinearMap x' = (M.xMul j ^ k) x) (m : ℤ) :
    ∀ (j : Fin (n + 1)) (e : ℤ), ∀ x ∈ (M.shift m).grade e,
      ∃ k : ℕ, ∃ x' ∈ (M'.shift m).grade (e + k),
        (ψ.shift m).toLinearMap x' = ((M.shift m).xMul j ^ k) x := by
  intro j e x hx
  obtain ⟨k, x', hx', heq⟩ := hsat j (e + m) x hx
  refine ⟨k, x', ?_, heq⟩
  change x' ∈ M'.grade (e + k + m)
  rw [add_right_comm]; exact hx'

end HomLemmas

section PowUnit

variable {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
  (φ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A
local notation "MM" => ProjSpace.twistGradedModule φ (φ ≫ ProjSpace.π A n)

theorem X_pow_mul_mem (j : Fin (n + 1)) (t d : ℕ) (p : ↥(𝒜 d)) : X j ^ t * p.1 ∈ 𝒜 (d + t) := by
  have h := SetLike.mul_mem_graded (SetLike.pow_mem_graded t (ProjSpace.X_mem_one A n j)) p.2
  rwa [smul_eq_mul, mul_one, Nat.add_comm t d] at h

theorem xMul_pow_unitFam (j : Fin (n + 1)) (t d : ℕ) (p : ↥(𝒜 d)) :
    ((MM).xMul j ^ t) (unitFam φ d p) = unitFam φ (d + t) ⟨X j ^ t * p.1, X_pow_mul_mem j t d p⟩ :=
      by
  induction t with
  | zero =>
    erw [pow_zero, Module.End.one_apply]
    apply unitFam_congr φ (by omega)
    change (p : MvPolynomial (Fin (n + 1)) A) = X j ^ 0 * (p : MvPolynomial (Fin (n + 1)) A)
    rw [pow_zero, one_mul]
  | succ t ih =>
    erw [pow_succ', Module.End.mul_apply, ih, xMul_unitFam]
    exact unitFam_congr φ (by omega) _ _ (by simp only; ring)

end PowUnit

section Extract2

variable {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
  (φ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))

local notation "MM" => ProjSpace.twistGradedModule φ (φ ≫ ProjSpace.π A n)

theorem apply_eq_of_globSec_vtx_eq (d : ℕ) (x y : ProjSpace.twistFam (φ ≫ ProjSpace.π A n) φ)
    (hx : x ∈ ((MM).shift (d : ℤ)).grade (∑ j : Fin (n + 1), (((0 : Fin (n + 1) → ℕ) j : ℕ) : ℤ)))
    (hy : y ∈ ((MM).shift (d : ℤ)).grade (∑ j : Fin (n + 1), (((0 : Fin (n + 1) → ℕ) j : ℕ) : ℤ)))
    (i : Fin (n + 1))
    (h : globSec ((MM).shift (d : ℤ)) (ProjSpaceCech.Idx.img n (vtx i)) x hx =
      globSec ((MM).shift (d : ℤ)) (ProjSpaceCech.Idx.img n (vtx i)) y hy) :
    x (d : ℤ) i = y (d : ℤ) i := by
  rw [img_vtx] at h
  exact apply_eq_of_globSec_eq φ d x y hx hy i h

end Extract2

end PolySurjBody

end

end AlgebraicCurves.Geometry.Projective.Proofs.ProjSpaceHomogeneousGradeLift

namespace AlgebraicGeometry.ProjSpace

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.MvPolynomial
open _root_.TensorProduct
open _root_.HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

open _root_.AlgebraicCurves.Geometry.Projective.Proofs.ProjSpaceHomogeneousGradeLift in
open PolySurjBody in
theorem exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion
    {A : Type u} [CommRing A] [IsNoetherianRing A] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsClosedImmersion ι] :
    ∃ d₂ : ℕ, ∀ d : ℕ, d₂ ≤ d →
      ∀ x : ProjSpace.twistFam (ι ≫ ProjSpace.π A n) ι,
        x ∈ (ProjSpace.twistGradedModule ι (ι ≫ ProjSpace.π A n)).grade (d : ℤ) →
        ∃ (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d),
          ∀ i : Fin (n + 1),
            x (d : ℤ) i =
              ProjSpace.restrictFun
                (inf_le_right : (⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart ι i ≤
                  ProjSpace.pullbackChart ι i)
                ((ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
                  (MvPolynomial.X i)))
                  (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
                    (MvPolynomial.X i)
                    (HomogeneousLocalization.mk
                      { deg := d
                        num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                        den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d
                          _).mpr
                          (MvPolynomial.isHomogeneous_X_pow i d)⟩
                        den_mem := ⟨d, rfl⟩ }))) := by
  classical
  obtain ⟨D', ψ, ⟨σ⟩, hinj, hsat⟩ :=
    AlgebraicGeometry.ProjSpace.exists_isFG_hom_injective_saturated_twistGradedModule ι (ι ≫
      ProjSpace.π A n) rfl
  obtain ⟨dS, hdS⟩ := ProjSpaceCech.GradedModule.exists_forall_H_zero_shift_eq_sec_mk_of_isFG D' ⟨σ⟩
  have hgen : ∀ (k : σ.J) (j : Fin (n + 1)), ∃ (K : ℕ) (F : MvPolynomial (Fin (n + 1)) A)
      (hF : F ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A ((-(σ.d₀ k)).toNat + K)),
      0 ≤ -(σ.d₀ k) →
      ((ProjSpace.twistGradedModule ι (ι ≫ ProjSpace.π A n)).xMul j ^ K)
        (ψ.toLinearMap (σ.hom.toLinearMap (Pi.single k (1 : MvPolynomial (Fin (n + 1)) A)))) =
          unitFam ι ((-(σ.d₀ k)).toNat + K) ⟨F, hF⟩ := by
    intro k j
    by_cases hneg : 0 ≤ -(σ.d₀ k)
    · set y := ψ.toLinearMap (σ.hom.toLinearMap (Pi.single k (1 : MvPolynomial (Fin (n + 1)) A)))
        with hy
      have hgk : (Pi.single k (1 : MvPolynomial (Fin (n + 1)) A)) ∈ σ.F.grade (-(σ.d₀ k)) := by
        intro k' _
        change (Pi.single k (1 : MvPolynomial (Fin (n + 1)) A) :
          σ.J → MvPolynomial (Fin (n + 1)) A) k' ∈
            ProjSpaceCech.GradedModule.freeGrade A n (-(σ.d₀ k) + σ.d₀ k')
        by_cases hk : k' = k
        · subst hk
          rw [Pi.single_eq_same]
          show (1 : MvPolynomial (Fin (n + 1)) A) ∈ ProjSpaceCech.GradedModule.freeGrade A n
            (-(σ.d₀ k') + σ.d₀ k')
          rw [neg_add_cancel, ProjSpaceCech.GradedModule.freeGrade_of_nonneg A n le_rfl,
            Int.toNat_zero,
            MvPolynomial.mem_homogeneousSubmodule]
          exact MvPolynomial.isHomogeneous_one (Fin (n + 1)) A
        · rw [Pi.single_eq_of_ne hk]
          exact Submodule.zero_mem _
      have hymem : y ∈ (ProjSpace.twistGradedModule ι (ι ≫ ProjSpace.π A n)).grade (-(σ.d₀ k)) :=
        ψ.mem_grade _ _ (σ.hom.mem_grade _ _ hgk)
      obtain ⟨K, F, hF, hKF⟩ :=
        exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion
          ι (-(σ.d₀ k)).toNat y
          (by rwa [Int.toNat_of_nonneg hneg]) j
      refine ⟨K, F, (MvPolynomial.mem_homogeneousSubmodule _ F).mpr hF, fun _ => ?_⟩
      funext d' i
      by_cases hd' : d' = (((-(σ.d₀ k)).toNat + K : ℕ) : ℤ)
      · subst hd'
        rw [hKF i, unitFam_apply_self]
        rfl
      · rw [unitFam_apply_ne ι _ _ d' hd']
        have hz : ((ProjSpace.twistGradedModule ι (ι ≫ ProjSpace.π A n)).xMul j ^ K) y ∈
            (ProjSpace.twistGradedModule ι (ι ≫ ProjSpace.π A n)).grade (-(σ.d₀ k) + K) :=
          ProjSpaceCech.GradedModule.xMul_pow_mem_grade _ j K _ y hymem
        have hz1 := hz.1 d' (by
          intro h; apply hd'; rw [h]; push_cast; rw [Int.toNat_of_nonneg hneg])
        exact congrFun hz1 i
    · exact ⟨0, 0, Submodule.zero_mem _, fun h => absurd h hneg⟩
  choose Kf Ff hFf hKf using hgen
  let K : ℕ := ∑ k, ∑ j, Kf k j + ∑ k, (σ.d₀ k).toNat
  have hKle : ∀ k j, Kf k j ≤ K := fun k j =>
    ((Finset.single_le_sum (fun j _ => Nat.zero_le (Kf k j)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun j _ => Nat.zero_le (Kf k j))
        (Finset.mem_univ k))).trans
      (Nat.le_add_right _ _)
  have hKd : ∀ k, σ.d₀ k ≤ (K : ℤ) := fun k => by
    have h1 : (σ.d₀ k).toNat ≤ K :=
      (Finset.single_le_sum (fun k _ => Nat.zero_le ((σ.d₀ k).toNat)) (Finset.mem_univ k)).trans
        (Nat.le_add_left _ _)
    have h2 : σ.d₀ k ≤ ((σ.d₀ k).toNat : ℤ) := Int.self_le_toNat _
    omega
  let e : σ.J → ℕ := fun k => ((K : ℤ) - σ.d₀ k).toNat
  have he : ∀ k, (e k : ℤ) = (K : ℤ) - σ.d₀ k := fun k => Int.toNat_of_nonneg
    (by have := hKd k; omega)
  have hK : ∀ (k : σ.J) (j : Fin (n + 1)), ∃ (F : MvPolynomial (Fin (n + 1)) A)
      (hF : F ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A (e k)),
      ((ProjSpace.twistGradedModule ι (ι ≫ ProjSpace.π A n)).xMul j ^ K)
        (ψ.toLinearMap (σ.hom.toLinearMap (Pi.single k (1 : MvPolynomial (Fin (n + 1)) A)))) =
          unitFam ι (e k) ⟨F, hF⟩ := by
    intro k j
    by_cases hneg : 0 ≤ -(σ.d₀ k)
    · obtain ⟨t, ht⟩ : ∃ t : ℕ, K = Kf k j + t := ⟨K - Kf k j, by have := hKle k j; omega⟩
      have hdeg : (-(σ.d₀ k)).toNat + Kf k j + t = e k := by
        have h1 := he k
        have h2 : (((-(σ.d₀ k)).toNat : ℕ) : ℤ) = -(σ.d₀ k) := Int.toNat_of_nonneg hneg
        omega
      refine ⟨X j ^ t * Ff k j, hdeg ▸ X_pow_mul_mem j t _ ⟨Ff k j, hFf k j⟩, ?_⟩
      rw [ht, add_comm (Kf k j) t, pow_add, Module.End.mul_apply, hKf k j hneg, xMul_pow_unitFam]
      exact unitFam_congr ι hdeg _ _ rfl
    · set y := ψ.toLinearMap (σ.hom.toLinearMap (Pi.single k (1 : MvPolynomial (Fin (n + 1)) A)))
        with hy
      have hgk : (Pi.single k (1 : MvPolynomial (Fin (n + 1)) A)) ∈ σ.F.grade (-(σ.d₀ k)) := by
        intro k' _
        change (Pi.single k (1 : MvPolynomial (Fin (n + 1)) A) :
          σ.J → MvPolynomial (Fin (n + 1)) A) k' ∈
            ProjSpaceCech.GradedModule.freeGrade A n (-(σ.d₀ k) + σ.d₀ k')
        by_cases hk : k' = k
        · subst hk
          rw [Pi.single_eq_same]
          show (1 : MvPolynomial (Fin (n + 1)) A) ∈ ProjSpaceCech.GradedModule.freeGrade A n
            (-(σ.d₀ k') + σ.d₀ k')
          rw [neg_add_cancel, ProjSpaceCech.GradedModule.freeGrade_of_nonneg A n le_rfl,
            Int.toNat_zero,
            MvPolynomial.mem_homogeneousSubmodule]
          exact MvPolynomial.isHomogeneous_one (Fin (n + 1)) A
        · rw [Pi.single_eq_of_ne hk]
          exact Submodule.zero_mem _
      have hymem : y ∈ (ProjSpace.twistGradedModule ι (ι ≫ ProjSpace.π A n)).grade (-(σ.d₀ k)) :=
        ψ.mem_grade _ _ (σ.hom.mem_grade _ _ hgk)
      have hy0 : y = 0 := by
        have h1 := hymem.1
        have h2 := hymem.2.1 (by omega)
        funext d' i
        by_cases hd' : d' = -(σ.d₀ k)
        · subst hd'; exact congrFun h2 i
        · exact congrFun (h1 d' hd') i
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      rw [hy0, map_zero]
      have h0 := unitFam_smul ι (e k) (0 : A) ⟨0, Submodule.zero_mem _⟩
      rw [zero_smul, zero_smul] at h0
      have e0 : (⟨0, Submodule.zero_mem _⟩ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A (e
        k))) = 0 := rfl
      rw [e0]
      exact h0.symm
  obtain ⟨d₁, hd₁⟩ := absorb ι K σ ψ e he hK
  refine ⟨(max dS d₁).toNat, fun d hd x hx => ?_⟩
  have hdS' : dS ≤ (d : ℤ) := by have := le_max_left dS d₁; omega
  have hd₁' : d₁ ≤ (d : ℤ) := by have := le_max_right dS d₁; omega
  have hx0 : x ∈ ((ProjSpace.twistGradedModule ι (ι ≫ ProjSpace.π A n)).shift (d : ℤ)).grade
      (∑ j : Fin (n + 1), (((0 : Fin (n + 1) → ℕ) j : ℕ) : ℤ)) := by
    change x ∈ (ProjSpace.twistGradedModule ι (ι ≫ ProjSpace.π A n)).grade (_ + d)
    simpa using hx
  have hbij := ProjSpaceCech.GradedModule.Hom.HMap_bijective_of_saturated (ψ.shift (d : ℤ)) hinj
    (sat_shift ψ hsat d) 0
  obtain ⟨c', hc'⟩ := hbij.2 (globCocycle _ x hx0)
  obtain ⟨m', hm'd, hm', hcs⟩ := hdS (d : ℤ) hdS' c'
  have hy0 : ψ.toLinearMap m' ∈ ((ProjSpace.twistGradedModule ι (ι ≫ ProjSpace.π A n)).shift (d :
    ℤ)).grade
      (∑ j : Fin (n + 1), (((0 : Fin (n + 1) → ℕ) j : ℕ) : ℤ)) := (ψ.shift (d : ℤ)).mem_grade _ _
        hm'
  obtain ⟨G, hG, hψ⟩ := hd₁ d hd₁' m' hm'd
  refine ⟨G, (MvPolynomial.mem_homogeneousSubmodule d G).mp hG, fun i => ?_⟩
  have key : x (d : ℤ) i = (ψ.toLinearMap m') (d : ℤ) i := by
    apply apply_eq_of_globSec_vtx_eq ι d x (ψ.toLinearMap m') hx0 hy0 i
    have h1 : ProjSpaceCech.GradedModule.Hom.secMap (ψ.shift (d : ℤ)) (ProjSpaceCech.Idx.img n (vtx
      i))
        ((show ↥(LinearMap.ker (ProjSpaceCech.GradedModule.d (D'.shift (d : ℤ)) 0)) from c').1 (vtx
          i)) =
        globSec ((ProjSpace.twistGradedModule ι (ι ≫ ProjSpace.π A n)).shift (d : ℤ))
          (ProjSpaceCech.Idx.img n (vtx i)) x hx0 :=
      congrArg (fun c : ProjSpaceCech.GradedModule.H _ 0 =>
        (show ↥(LinearMap.ker (ProjSpaceCech.GradedModule.d
          ((ProjSpace.twistGradedModule ι (ι ≫ ProjSpace.π A n)).shift (d : ℤ)) 0)) from c).1 (vtx
            i)) hc'
    rw [hcs (vtx i), secMap_mk] at h1
    exact h1.symm
  rw [key, hψ, unitFam_apply_self]
  rfl

end AlgebraicGeometry.ProjSpace
end ProofImplementation
