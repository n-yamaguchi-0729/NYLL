/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Geometry.Projective.HomogeneousChartSections
public import Nyll.AlgebraicCurves.Geometry.Projective.ChartSectionsBaseChange
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic.Ext
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.Tactic.Ring
public import Nyll.SchemeTheory.ProjectiveSpace.Basic
public import Nyll.SchemeTheory.ProjectiveSpace.Cover
public import Nyll.AlgebraicCurves.Geometry.Projective.ProjTwistDatum
public import Nyll.AlgebraicCurves.Geometry.Schemes.Covers.OrderedAffineCoverComap
public import Nyll.AlgebraicCurves.Geometry.Schemes.Sections.IsAffineOpenLinearEquivTensorSections
public import Nyll.SchemeTheory.ProjectiveSpace.StandardChartsBaseChange

/-!
# Proj Space mem map iff forall app away To Section eq zero of base Change field
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Projective.Proofs
namespace ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

open HomogeneousLocalization

namespace RM7Aux

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

section Setup

variable {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
  (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsAffineHom ι]
  (B : Type u) [CommRing B] [Algebra A B] {Z' : Scheme.{u}}
  (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)) [IsAffineHom ι']
  (e : Z' ⟶ Z)

local notation "𝒜A" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A
local notation "𝒜B" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B

omit [IsAffineHom ι] [IsAffineHom ι'] in
theorem preimage_pullbackChart (hcomp : e ≫ ι = ι' ≫ ProjSpace.map A B n) (j : Fin (n + 1)) :
    e ⁻¹ᵁ ProjSpace.pullbackChart ι j = ProjSpace.pullbackChart ι' j :=
  ProjSpace.ChartSectionsBaseChange.preimage_pullbackChart ι B ι' e hcomp j

theorem X_eq_mvMapGraded_mul_one (i : Fin (n + 1)) :
    (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) B) = (ProjSpace.mvMapGraded A B n)
      (MvPolynomial.X i) * 1 :=
  ProjSpace.ChartSectionsBaseChange.X_eq_mvMapGraded_mul_one (A := A) B i

theorem one_mem_zero : (1 : MvPolynomial (Fin (n + 1)) B) ∈ (MvPolynomial.homogeneousSubmodule (Fin
  (n + 1)) B) 0 :=
  ProjSpace.ChartSectionsBaseChange.one_mem_zero (n := n) B

/-- The coordinate localization map induced by the coefficient base change. -/
noncomputable def toB (i : Fin (n + 1)) : Away 𝒜A (MvPolynomial.X i) →+* Away 𝒜B (MvPolynomial.X i)
  :=
  ProjSpace.ChartSectionsBaseChange.toB (A := A) B i

theorem toB_ratio (i j : Fin (n + 1)) : toB (A := A) B i (ProjSpace.ratio A n i j) =
  ProjSpace.ratio B n i j :=
  ProjSpace.ChartSectionsBaseChange.toB_ratio (A := A) B i j
omit [IsAffineHom ι] [IsAffineHom ι'] in
theorem restrictFun_app_pullAway (hcomp : e ≫ ι = ι' ≫ ProjSpace.map A B n) (i : Fin (n + 1))
    (a : Away 𝒜A (MvPolynomial.X i)) {W' : Z'.Opens}
    (h₁ : W' ≤ e ⁻¹ᵁ ProjSpace.pullbackChart ι i) (h₂ : W' ≤ ProjSpace.pullbackChart ι' i) :
    ProjSpace.restrictFun h₁ ((e.app (ProjSpace.pullbackChart ι i)).hom
        ((ι.app (Proj.basicOpen 𝒜A (MvPolynomial.X i))).hom ((Proj.awayToSection 𝒜A (MvPolynomial.X
          i)).hom a)))
      = ProjSpace.restrictFun h₂ ((ι'.app (Proj.basicOpen 𝒜B (MvPolynomial.X i))).hom
          ((Proj.awayToSection 𝒜B (MvPolynomial.X i)).hom (toB (A := A) B i a))) :=
  ProjSpace.ChartSectionsBaseChange.restrictFun_app_pullAway ι B ι' e hcomp i a h₁ h₂
omit [IsAffineHom ι] [IsAffineHom ι'] in
theorem restrictFun_app_frameUnit (hcomp : e ≫ ι = ι' ≫ ProjSpace.map A B n) (i j : Fin (n + 1))
  {W' : Z'.Opens}
    (h₁ : W' ≤ e ⁻¹ᵁ ProjSpace.pullbackChart ι i) (h₂ : W' ≤ ProjSpace.pullbackChart ι' i) :
    ProjSpace.restrictFun h₁ ((e.app (ProjSpace.pullbackChart ι i)).hom (ProjSpace.frameUnit ι i j))
      = ProjSpace.restrictFun h₂ (ProjSpace.frameUnit ι' i j) :=
  ProjSpace.ChartSectionsBaseChange.restrictFun_app_frameUnit ι B ι' e hcomp i j h₁ h₂

theorem restrictFun_app_eq {U V : Z.Opens} (hVU : V ≤ U) {W' : Z'.Opens} (h₁ : W' ≤ e ⁻¹ᵁ V) (h₂ :
  W' ≤ e ⁻¹ᵁ U)
    (x : Γ(Z, U)) :
    ProjSpace.restrictFun h₁ ((e.app V).hom (ProjSpace.restrictFun hVU x)) = ProjSpace.restrictFun
      h₂ ((e.app U).hom x) :=
  ProjSpace.ChartSectionsBaseChange.restrictFun_app_eq e hVU h₁ h₂ x

theorem appLE_top_top {X Y : Scheme.{u}} (g : X ⟶ Y) (h : (⊤ : X.Opens) ≤ g ⁻¹ᵁ ⊤) : g.appLE ⊤ ⊤ h
  = g.appTop := by
  rw [Scheme.Hom.appLE]
  have : (homOfLE h).op = 𝟙 _ := Subsingleton.elim _ _
  rw [this]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

theorem appLE_hom_apply {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (h : V ≤ g ⁻¹ᵁ
  U) (x : Γ(Y, U)) :
    (g.appLE U V h).hom x = ProjSpace.restrictFun h ((g.app U).hom x) := rfl

theorem toB_mkDeg (i : Fin (n + 1)) (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF :
  F.IsHomogeneous d) :
    toB (A := A) B i (HomogeneousLocalization.mk
        { deg := d
          num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
          den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
            (MvPolynomial.isHomogeneous_X_pow i d)⟩
          den_mem := ⟨d, rfl⟩ } : Away 𝒜A (MvPolynomial.X i)) =
      (HomogeneousLocalization.mk
        { deg := d
          num := ⟨MvPolynomial.map (algebraMap A B) F,
            (MvPolynomial.mem_homogeneousSubmodule d _).mpr (hF.map (algebraMap A B))⟩
          den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
            (MvPolynomial.isHomogeneous_X_pow i d)⟩
          den_mem := ⟨d, rfl⟩ } : Away 𝒜B (MvPolynomial.X i)) :=
  ProjSpace.ChartSectionsBaseChange.toB_mkDeg (A := A) B i d F hF

end Setup

section Dehom

variable {k : Type u} [CommRing k] {n : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

/--
The dehomogenization homomorphism sending each projective coordinate to its ratio with
coordinate `i`.
-/
noncomputable def dehom (k : Type u) [CommRing k] {n : ℕ} (i : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) k →ₐ[k] Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (X
      i) :=
  MvPolynomial.aeval (fun j => ProjSpace.ratio k n i j)

theorem dehom_X (i j : Fin (n + 1)) : dehom k i (X j : MvPolynomial (Fin (n + 1)) k) =
  ProjSpace.ratio k n i j :=
  MvPolynomial.aeval_X _ j

theorem dehom_C (i : Fin (n + 1)) (r : k) : dehom k i (C r : MvPolynomial (Fin (n + 1)) k) =
  algebraMap k (Away 𝒜 (X i)) r :=
  MvPolynomial.aeval_C _ r

theorem val_dehom (i : Fin (n + 1)) {q : ℕ} {G : MvPolynomial (Fin (n + 1)) k} (hG :
  G.IsHomogeneous q) :
    (dehom k i G).val = Localization.mk G (⟨X i ^ q, ⟨q, rfl⟩⟩ : Submonoid.powers (X i :
      MvPolynomial (Fin (n + 1)) k)) := by
  classical
  have hval : (HomogeneousLocalization.val : Away 𝒜 (X i) → Localization.Away (X i : MvPolynomial
    (Fin (n + 1)) k))
      = algebraMap (Away 𝒜 (X i)) (Localization.Away (X i : MvPolynomial (Fin (n + 1)) k)) := rfl
  have hdeg : ∀ α ∈ G.support, (α : Fin (n + 1) →₀ ℕ).degree = q := fun α hα => by
    rw [Finsupp.degree_eq_weight_one]; exact hG (mem_support_iff.mp hα)
  conv_lhs => rw [G.as_sum, map_sum, hval, map_sum]
  conv_rhs => rw [G.as_sum, Localization.mk_sum]
  refine Finset.sum_congr rfl (fun α hα => ?_)
  rw [← hval, dehom, MvPolynomial.aeval_monomial,
    Finsupp.prod_fintype _ _ (fun j => pow_zero _),
    ← ProjSpace.awayMk_monomial k n i q α (hdeg α hα) (G.coeff α), Away.val_mk]
  exact (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
    (MvPolynomial.isHomogeneous_monomial _ (by simp only [smul_eq_mul, mul_one]; exact hdeg α hα))

theorem dehom_eq_frac (i : Fin (n + 1)) {q : ℕ} {G : MvPolynomial (Fin (n + 1)) k} (hG :
  G.IsHomogeneous q) :
    dehom k i G = frac q ⟨G, (MvPolynomial.mem_homogeneousSubmodule q G).mpr hG⟩ i :=
  HomogeneousLocalization.val_injective _ (by rw [val_dehom i hG, val_frac])

end Dehom

section Chart

variable {k : Type u} [CommRing k] {n : ℕ} {Z : Scheme.{u}}
  (φ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

/-- The homomorphism evaluating dehomogenized polynomials as sections on the pulled-back chart. -/
noncomputable def chartHom (i : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) k →+* Γ(Z,
  ProjSpace.pullbackChart φ i) :=
  (((φ.app (Proj.basicOpen 𝒜 (X i))).hom.comp (Proj.awayToSection 𝒜 (X i)).hom).comp (dehom k
    i).toRingHom)

theorem chartHom_apply (i : Fin (n + 1)) (G : MvPolynomial (Fin (n + 1)) k) :
    chartHom φ i G = pullAway φ i (dehom k i G) := rfl

theorem chartHom_eq_zero_of_mem (i : Fin (n + 1)) (m : ℕ) (J : Ideal (MvPolynomial (Fin (n + 1)) k))
    (hJ : ∀ p ∈ J, ∀ e : ℕ, MvPolynomial.homogeneousComponent e p ∈ J)
    (hZ : ∀ (q : ℕ), m ≤ q → ∀ (p : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k q)),
      (p : MvPolynomial (Fin (n + 1)) k) ∈ J → pullAway φ i (frac q p i) = 0)
    (G : MvPolynomial (Fin (n + 1)) k) (hG : G ∈ J) : chartHom φ i G = 0 := by
  classical
  rw [← MvPolynomial.sum_homogeneousComponent G, map_sum]
  refine Finset.sum_eq_zero fun q _ => ?_
  have hq : (homogeneousComponent q G).IsHomogeneous q := homogeneousComponent_isHomogeneous q G
  have hqJ := hJ G hG q
  rcases le_or_gt m q with hmq | hqm
  · rw [chartHom_apply, dehom_eq_frac i hq]
    exact hZ q hmq ⟨_, _⟩ hqJ
  · have hH : (X i ^ (m - q) * homogeneousComponent q G).IsHomogeneous m := by
      have := (isHomogeneous_X_pow i (m - q)).mul hq
      rwa [Nat.sub_add_cancel hqm.le] at this
    have hHJ : X i ^ (m - q) * homogeneousComponent q G ∈ J := J.mul_mem_left _ hqJ
    have h0 := hZ m le_rfl ⟨_, (MvPolynomial.mem_homogeneousSubmodule m _).mpr hH⟩ hHJ
    rw [← dehom_eq_frac i hH, map_mul, map_pow, dehom_X, ProjSpace.ratio_self, one_pow, one_mul]
      at h0
    rwa [chartHom_apply]

end Chart

section BC

variable {A : Type u} [CommRing A] {n : ℕ} (B : Type u) [CommRing B] [Algebra A B]

theorem toB_frac (i : Fin (n + 1)) (q : ℕ) (G : MvPolynomial (Fin (n + 1)) A) (hG : G.IsHomogeneous
  q) :
    toB (A := A) B i (frac q ⟨G, (MvPolynomial.mem_homogeneousSubmodule q G).mpr hG⟩ i)
      = frac q ⟨MvPolynomial.map (algebraMap A B) G,
          (MvPolynomial.mem_homogeneousSubmodule q _).mpr (hG.map (algebraMap A B))⟩ i :=
  toB_mkDeg B i q G hG

theorem toB_dehom (i : Fin (n + 1)) (G : MvPolynomial (Fin (n + 1)) A) :
    toB (A := A) B i (dehom A i G) = dehom B i (MvPolynomial.map (algebraMap A B) G) := by
  have key : (toB (A := A) B i).comp (dehom A i).toRingHom
      = (dehom B i).toRingHom.comp (MvPolynomial.map (algebraMap A B)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        MvPolynomial.map_C]
      have hA : (C r : MvPolynomial (Fin (n + 1)) A).IsHomogeneous 0 :=
        MvPolynomial.isHomogeneous_C _ _
      have hB : (C (algebraMap A B r) : MvPolynomial (Fin (n + 1)) B).IsHomogeneous 0 :=
        MvPolynomial.isHomogeneous_C _ _
      rw [dehom_eq_frac i hA, dehom_eq_frac i hB, toB_frac B i 0 (C r) hA]
      congr 2
      exact MvPolynomial.map_C _ r
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        MvPolynomial.map_X]
      rw [dehom_X, dehom_X, toB_ratio]
  exact congrArg (fun ψ : MvPolynomial (Fin (n + 1)) A →+* _ => ψ G) key

end BC

end RM7Aux


end ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field
end AlgebraicCurves.Geometry.Projective.Proofs

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits MvPolynomial TensorProduct HomogeneousLocalization
universe u
attribute [local instance] MvPolynomial.gradedAlgebra


open _root_.AlgebraicCurves.Geometry.Projective.Proofs in
open ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field in
open RM7Aux in
theorem ProjSpace.mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field
    {k : Type u} [Field k] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsAffineHom ι]
    (K : Type u) [Field K] [Algebra k K] {Z' : Scheme.{u}}
    (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)) [IsAffineHom ι']
    (e : Z' ⟶ Z)
    (hpb : IsPullback e (ι' ≫ ProjSpace.π K n) (ι ≫ ProjSpace.π k n) (Spec.map (CommRingCat.ofHom
      (algebraMap k K))))
    (hcomp : e ≫ ι = ι' ≫ ProjSpace.map k K n) (m : ℕ)
    (J : Ideal (MvPolynomial (Fin (n + 1)) k)) (hJ : ∀ p ∈ J, ∀ e : ℕ,
      MvPolynomial.homogeneousComponent e p ∈ J)
    (hZ : ∀ (d : ℕ), m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
        (F ∈ J ↔ ∀ i : Fin (n + 1), ((ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin
          (n + 1)) k) (MvPolynomial.X i)))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
                (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ }))) = 0)) :
    ∀ (d : ℕ), m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) K) (hF : F.IsHomogeneous d),
        (F ∈ J.map (MvPolynomial.map (algebraMap k K)) ↔ ∀ i : Fin (n + 1), ((ι'.app
          (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i)))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
                (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ }))) = 0) := by
  classical
  intro d hmd F hF
  have hZ' : ∀ (q : ℕ), m ≤ q → ∀ (p : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k q)),
      ((p : MvPolynomial (Fin (n + 1)) k) ∈ J ↔ ∀ i, pullAway ι i (frac q p i) = 0) :=
    fun q hq p => hZ q hq p.1 ((MvPolynomial.mem_homogeneousSubmodule q p.1).mp p.2)
  change F ∈ J.map (MvPolynomial.map (algebraMap k K)) ↔
    ∀ i, pullAway ι' i (frac d ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ i) = 0
  have hpre : ∀ i, e ⁻¹ᵁ ProjSpace.pullbackChart ι i = ProjSpace.pullbackChart ι' i :=
    fun i => preimage_pullbackChart ι K ι' e hcomp i
  have htrans : ∀ (i : Fin (n + 1)) (a : Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
    (X i)),
      pullAway ι' i (toB (A := k) K i a)
        = ProjSpace.restrictFun (hpre i).ge ((e.app (ProjSpace.pullbackChart ι i)).hom (pullAway ι
          i a)) := by
    intro i a
    have := restrictFun_app_pullAway ι K ι' e hcomp i a (hpre i).ge le_rfl
    erw [ProjSpace.restrictFun_refl] at this
    exact this.symm
  have hkill : ∀ (i : Fin (n + 1)) (G : MvPolynomial (Fin (n + 1)) k), G ∈ J → chartHom ι i G = 0 :=
    fun i G hG => chartHom_eq_zero_of_mem ι i m J hJ (fun q hq p hp => (hZ' q hq p).mp hp i) G hG
  have hkill' : ∀ i, J.map (MvPolynomial.map (algebraMap k K)) ≤ RingHom.ker (chartHom ι' i) := by
    intro i
    rw [Ideal.map_le_iff_le_comap]
    intro G hG
    rw [Ideal.mem_comap, RingHom.mem_ker, chartHom_apply, ← toB_dehom, htrans, ← chartHom_apply,
      hkill i G hG,
      map_zero, map_zero]
  constructor
  · intro hFJ i
    have := hkill' i hFJ
    rwa [RingHom.mem_ker, chartHom_apply, dehom_eq_frac i hF] at this
  · intro hvan
    let instZ : ∀ U : Z.Opens, Algebra k Γ(Z, U) :=
      fun U => Scheme.TwoAffineOpenCover.algebraOfHom (ι ≫ ProjSpace.π k n) U
    let instS : ∀ V : (Spec (CommRingCat.of K)).Opens, Algebra k Γ(Spec (CommRingCat.of K), V) :=
      fun V => Scheme.TwoAffineOpenCover.algebraOfHom (Spec.map (CommRingCat.ofHom (algebraMap k
        K))) V
    let instZ' : ∀ W : Z'.Opens, Algebra k Γ(Z', W) :=
      fun W => Scheme.TwoAffineOpenCover.algebraOfHom (e ≫ (ι ≫ ProjSpace.π k n)) W
    let U : Fin (n + 1) → Z.Opens := fun i => ProjSpace.pullbackChart ι i
    let p₂ : Z' ⟶ Spec (CommRingCat.of K) := ι' ≫ ProjSpace.π K n
    let W : Fin (n + 1) → Z'.Opens := fun i => e ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ ⊤
    have hW₁ : ∀ i, W i ≤ e ⁻¹ᵁ ProjSpace.pullbackChart ι i := fun i => inf_le_left
    have hW₂ : ∀ i, W i ≤ ProjSpace.pullbackChart ι' i := fun i => inf_le_left.trans (hpre i).le
    have hBC : ∀ i, ∃ Φ : Γ(Z, U i) ⊗[k] Γ(Spec (CommRingCat.of K), (⊤ : (Spec (CommRingCat.of
      K)).Opens)) ≃ₗ[k] Γ(Z', W i),
        ∀ (a : Γ(Z, U i)) (b : Γ(Spec (CommRingCat.of K), (⊤ : (Spec (CommRingCat.of K)).Opens))),
          Φ (a ⊗ₜ[k] b) =
          (e.appLE (U i) (W i) inf_le_left).hom a * (p₂.appLE ⊤ (W i) inf_le_right).hom b :=
      fun i =>
        (AlgebraicGeometry.Scheme.isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback
        (ι ≫ ProjSpace.π k n) (Spec.map (CommRingCat.ofHom (algebraMap k K))) e p₂ hpb (U i)
        (ProjSpace.isAffineOpen_pullbackChart ι i) ⊤ (isAffineOpen_top (Spec (CommRingCat.of K)))).2
    choose Φ hΦ using hBC
    have hκalg : ∀ a : k, (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (algebraMap k K a) = (instS
      ⊤).algebraMap a := by
      intro a
      erw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom, appLE_top_top]
      have nat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k K))
      have := congrArg (fun ψ => ψ.hom a) nat
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
      exact this
    obtain ⟨κ, hκ⟩ : ∃ κ : K ≃ₗ[k] Γ(Spec (CommRingCat.of K), (⊤ : (Spec (CommRingCat.of
      K)).Opens)),
        ∀ b : K, κ b = (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom b :=
      ⟨AddEquiv.toLinearEquiv (Scheme.ΓSpecIso (CommRingCat.of
        K)).commRingCatIsoToRingEquiv.symm.toAddEquiv (by
        intro a b
        change (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a • b) = a • (Scheme.ΓSpecIso
          (CommRingCat.of K)).inv.hom b
        rw [Algebra.smul_def, map_mul, hκalg, Algebra.smul_def]), fun _ => rfl⟩
    have hΘsmul : ∀ (i : Fin (n + 1)) (c : k) (p : ↥(MvPolynomial.homogeneousSubmodule (Fin (n +
      1)) k d)),
        pullAway ι i (frac d (c • p) i) = c • pullAway ι i (frac d p i) := by
      intro i c p
      rw [frac_smul, pullAway_mul, Algebra.smul_def]
      congr 1
      have := pullAway_algebraMap ι i c (le_refl (ProjSpace.pullbackChart ι i))
      erw [ProjSpace.restrictFun_refl] at this
      exact this
    obtain ⟨Θ, hΘ⟩ : ∃ Θ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) →ₗ[k] (∀ i : Fin
      (n + 1), Γ(Z, U i)), ∀ (p : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) (i : Fin
      (n + 1)), Θ p i = pullAway ι i (frac d p i) :=
      ⟨LinearMap.pi fun i =>
        { toFun := fun p => pullAway ι i (frac d p i)
          map_add' := fun p q => by rw [frac_add, pullAway_add]
          map_smul' := fun c p => hΘsmul i c p }, fun _ _ => rfl⟩
    have hexact : Function.Exact ((LinearMap.ker Θ).subtype.rTensor K) (Θ.rTensor K) :=
      Module.Flat.rTensor_exact (R := k) K (N := ↥(LinearMap.ker Θ))
        (N' := ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) (N'' := ∀ i : Fin (n + 1),
          Γ(Z, U i))
        (LinearMap.exact_subtype_ker_map Θ)
    obtain ⟨γ, hγ⟩ : ∃ γ : ∀ i, Γ(Z, U i) ⊗[k] K ≃ₗ[k] Γ(Z', W i), ∀ (i : Fin (n + 1)) (a : Γ(Z, U
      i)) (c : K),
        γ i (a ⊗ₜ[k] c) = (e.appLE (U i) (W i) inf_le_left).hom a *
          (p₂.appLE ⊤ (W i) inf_le_right).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c) := by
      refine ⟨fun i => TensorProduct.congr (LinearEquiv.refl k (Γ(Z, U i))) κ ≪≫ₗ Φ i, fun i a c =>
        ?_⟩
      change Φ i (TensorProduct.congr (LinearEquiv.refl k (Γ(Z, U i))) κ (a ⊗ₜ[k] c)) = _
      rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, hΦ, hκ]
    obtain ⟨Γf, hΓf⟩ : ∃ Γf : (∀ i : Fin (n + 1), Γ(Z, U i)) ⊗[k] K →ₗ[k] (∀ i : Fin (n + 1), Γ(Z',
      W i)),
        ∀ z i, Γf z i = γ i (((LinearMap.proj i : (∀ j, Γ(Z, U j)) →ₗ[k] Γ(Z, U i)).rTensor K) z) :=
      ⟨LinearMap.pi fun i => (γ i).toLinearMap ∘ₗ (LinearMap.proj i : (∀ j, Γ(Z, U j)) →ₗ[k] Γ(Z, U
        i)).rTensor K,
        fun _ _ => rfl⟩
    have hsplit : ∀ z : (∀ i : Fin (n + 1), Γ(Z, U i)) ⊗[k] K,
        ∑ i, ((LinearMap.single k (fun j => Γ(Z, U j)) i).rTensor K)
          (((LinearMap.proj i : (∀ j, Γ(Z, U j)) →ₗ[k] Γ(Z, U i)).rTensor K) z) = z := by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul a c =>
        simp only [LinearMap.rTensor_tmul, LinearMap.coe_proj, Function.eval, LinearMap.coe_single]
        rw [← TensorProduct.sum_tmul, Finset.univ_sum_single]
      | add x y hx hy => simp only [map_add, Finset.sum_add_distrib, hx, hy]
    have hΓinj : Function.Injective Γf := by
      intro x y hxy
      rw [← hsplit x, ← hsplit y]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      exact (γ i).injective (by rw [← hΓf, ← hΓf, hxy])
    let fV : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) →ₗ[k] MvPolynomial (Fin (n +
      1)) K :=
      { toFun := fun p => MvPolynomial.map (algebraMap k K) (p : MvPolynomial (Fin (n + 1)) k)
        map_add' := fun p q => by simp only [Submodule.coe_add, map_add]
        map_smul' := fun c p => by
          simp only [Submodule.coe_smul, RingHom.id_apply, MvPolynomial.smul_eq_C_mul, map_mul,
            MvPolynomial.map_C]
          rw [Algebra.smul_def, MvPolynomial.algebraMap_apply] }
    let gK : K →ₗ[k] MvPolynomial (Fin (n + 1)) K := (IsScalarTower.toAlgHom k K (MvPolynomial (Fin
      (n + 1)) K)).toLinearMap
    obtain ⟨β, hβ⟩ : ∃ β : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) ⊗[k] K →ₗ[k]
      MvPolynomial (Fin (n + 1)) K,
        ∀ (p : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) (c : K), β (p ⊗ₜ[k] c) =
          MvPolynomial.map (algebraMap k K) (p : MvPolynomial (Fin (n + 1)) k) * C c := by
      refine ⟨LinearMap.mul' k (MvPolynomial (Fin (n + 1)) K) ∘ₗ TensorProduct.map fV gK, fun p c
        => ?_⟩
      change LinearMap.mul' k _ (TensorProduct.map fV gK (p ⊗ₜ[k] c)) = _
      rw [TensorProduct.map_tmul, LinearMap.mul'_apply]
      change MvPolynomial.map (algebraMap k K) (p : MvPolynomial (Fin (n + 1)) k) *
        (IsScalarTower.toAlgHom k K (MvPolynomial (Fin (n + 1)) K)) c = _
      rw [IsScalarTower.toAlgHom_apply, MvPolynomial.algebraMap_eq]
    obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : MvPolynomial (Fin (n + 1)) K →+ ∀ i : Fin (n + 1), Γ(Z', W i),
        ∀ H i, Ψ H i = ProjSpace.restrictFun (hW₂ i) (chartHom ι' i H) :=
      ⟨{ toFun := fun H i => ProjSpace.restrictFun (hW₂ i) (chartHom ι' i H)
         map_zero' := funext fun i => by rw [map_zero, map_zero]; rfl
         map_add' := fun x y => funext fun i => by rw [map_add, map_add]; rfl }, fun _ _ => rfl⟩
    have hsq : ∀ z : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) ⊗[k] K, Γf ((Θ.rTensor
      K) z) = Ψ (β z) := by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul p c =>
        funext i
        rw [LinearMap.rTensor_tmul, hΓf, LinearMap.rTensor_tmul, LinearMap.coe_proj, Function.eval,
          hΘ, hγ, hβ, hΨ]
        rw [map_mul, map_mul, chartHom_apply, chartHom_apply, ← toB_dehom, dehom_C,
          dehom_eq_frac i ((MvPolynomial.mem_homogeneousSubmodule d (p : MvPolynomial (Fin (n + 1))
            k)).mp p.2),
          pullAway_algebraMap ι' i c (hW₂ i), Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom,
          htrans, ProjSpace.restrictFun_restrictFun]
        rfl
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    have hmon : ∀ α ∈ F.support, (MvPolynomial.monomial α (1 : k)) ∈
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d := by
      intro α hα
      refine (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_monomial _
        ?_)
      rw [Finsupp.degree_eq_weight_one]
      exact hF (MvPolynomial.mem_support_iff.mp hα)
    let t : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) ⊗[k] K := ∑ α ∈
      F.support.attach, (⟨MvPolynomial.monomial α.1 (1 : k), hmon α.1 α.2⟩ :
      ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) ⊗ₜ[k] F.coeff α.1
    have ht : β t = F := by
      change β (∑ α ∈ F.support.attach, (⟨MvPolynomial.monomial α.1 (1 : k), hmon α.1 α.2⟩ :
        ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) ⊗ₜ[k] F.coeff α.1) = F
      rw [map_sum]
      simp only [hβ, MvPolynomial.map_monomial, map_one]
      rw [Finset.sum_attach F.support (fun α => MvPolynomial.monomial α (1 : K) * C (F.coeff α))]
      conv_rhs => rw [F.as_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [mul_comm, MvPolynomial.C_mul_monomial, mul_one]
    have hΨF : Ψ F = 0 := by
      funext i
      rw [hΨ, Pi.zero_apply, chartHom_apply, dehom_eq_frac i hF, hvan i, map_zero]
    have h1 : (Θ.rTensor K) t = 0 := hΓinj (by rw [hsq, ht, hΨF, map_zero])
    obtain ⟨u, hu⟩ := (hexact t).mp h1
    have h2 : ∀ u : ↥(LinearMap.ker Θ) ⊗[k] K,
        β (((LinearMap.ker Θ).subtype.rTensor K) u) ∈ J.map (MvPolynomial.map (algebraMap k K)) :=
          by
      intro u
      induction u using TensorProduct.inductionOn with
      | tmul q c =>
        rw [LinearMap.rTensor_tmul, Submodule.subtype_apply, hβ]
        refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
        refine (hZ' d hmd q.1).mpr fun i => ?_
        have := congrFun (LinearMap.mem_ker.mp q.2) i
        rwa [hΘ] at this
      | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
    rw [← ht, ← hu]
    exact h2 u

end AlgebraicGeometry
end ProofImplementation
