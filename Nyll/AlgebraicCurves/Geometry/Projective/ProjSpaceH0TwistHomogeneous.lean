/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_isHomogeneous_of_baseChange_field.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Geometry.Projective.HomogeneousSectionsH0
public import Nyll.AlgebraicCurves.Geometry.Projective.ChartSectionsBaseChange
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic.Ext
public import Lean.Elab.Tactic.Omega
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Nyll.SchemeTheory.ProjectiveSpace.Basic
public import Nyll.SchemeTheory.ProjectiveSpace.Cover
public import Nyll.AlgebraicCurves.Geometry.Projective.ProjTwistDatum
public import Nyll.AlgebraicCurves.Geometry.Schemes.Covers.OrderedAffineCoverComap
public import Nyll.SchemeTheory.ProjectiveSpace.StandardChartsBaseChange
public import Nyll.AlgebraicCurves.Cohomology.Sheaves.BaseChange.ProjSpaceLinearEquivBaseChangeCochainTwist
public import Nyll.AlgebraicCurves.Geometry.Projective.ProjSpaceLinearMapHomogeneousSubmoduleTwistObjTopValEq

/-!
# Proj Space forall H0 twist exists is Homogeneous of base Change field
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Projective.Proofs
namespace ProjSpace_forall_H0_twist_exists_isHomogeneous_of_baseChange_field

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

open HomogeneousLocalization

namespace RM6Sol

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

theorem preimage_inter (hcomp : e ≫ ι = ι' ≫ ProjSpace.map A B n) {i : ℕ} (s :
  (ProjSpace.stdCoverPullback ι).Idx i) :
    e ⁻¹ᵁ (ProjSpace.stdCoverPullback ι).inter s = (ProjSpace.stdCoverPullback ι').inter s :=
  ProjSpace.ChartSectionsBaseChange.preimage_inter ι B ι' e hcomp s

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

section Theta

variable {n : ℕ} {k : Type u} [Field k] {Zk : Scheme.{u}}
  (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsAffineHom ιk] (d : ℕ)

/-- The section on a pulled-back projective chart obtained from the homogeneous polynomial. -/
noncomputable def chartVal (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d) (i : Fin (n
  + 1)) :
    Γ(Zk, ProjSpace.pullbackChart ιk i) :=
  ProjSpace.HomogeneousSectionsH0.chartVal ιk d F hF i

theorem isHomogeneous_of_mem (F : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) :
    (F : MvPolynomial (Fin (n + 1)) k).IsHomogeneous d :=
  ProjSpace.HomogeneousSectionsH0.isHomogeneous_of_mem d F

/-- The degree-zero Cech index corresponding to the selected standard projective chart. -/
def vertex (i : Fin (n + 1)) : (ProjSpace.stdCoverPullback ιk).Idx 0 :=
  ProjSpace.HomogeneousSectionsH0.vertex ιk i

theorem chart_le_inter_vertex (i : Fin (n + 1)) :
    ProjSpace.pullbackChart ιk i ≤ (ProjSpace.stdCoverPullback ιk).inter (vertex ιk i) ⊓
      ProjSpace.pullbackChart ιk i :=
  ProjSpace.HomogeneousSectionsH0.chart_le_inter_vertex ιk i

theorem exists_theta :
    ∃ Θ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) →ₗ[k]
        ↥((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).H0 (ProjSpace.stdCoverPullback ιk)),
      ∀ (F : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d))
        (s : (ProjSpace.stdCoverPullback ιk).Idx 0) (i : Fin (n + 1)),
        ((Θ F : (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).cochain (ProjSpace.stdCoverPullback
          ιk) 0) s).val i =
          ProjSpace.restrictFun
            (inf_le_right : (ProjSpace.stdCoverPullback ιk).inter s ⊓ ProjSpace.pullbackChart ιk i
              ≤ ProjSpace.pullbackChart ιk i)
            (chartVal ιk d F (isHomogeneous_of_mem d F) i) := by
  obtain ⟨θ, hθ, -⟩ := ProjSpace.exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq ιk d
  exact ProjSpace.HomogeneousSectionsH0.exists_theta_of_section_map ιk d θ hθ

end Theta

section LinAlg

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K] {V : Type u} [AddCommGroup V]
  [Module k V]

theorem eq_zero_of_one_tmul_eq_zero (v : V) (h : (1 : K) ⊗ₜ[k] v = 0) : v = 0 := by
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k K)
    (by rw [LinearMap.ker_eq_bot]; exact (algebraMap k K).injective)
  have h1 : TensorProduct.lid k V (TensorProduct.map ψ LinearMap.id ((1 : K) ⊗ₜ[k] v)) = v := by
    rw [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul]
    have : ψ 1 = 1 := by
      have := LinearMap.congr_fun hψ (1 : k)
      simpa using this
    rw [this, one_smul]
  rw [← h1, h, map_zero, map_zero]

theorem mem_of_one_tmul_mem_baseChange (W : Submodule k V) (v : V)
    (h : (1 : K) ⊗ₜ[k] v ∈ W.baseChange K) : v ∈ W := by
  refine (Submodule.Quotient.mk_eq_zero W).mp (eq_zero_of_one_tmul_eq_zero (k := k) K
    (Submodule.Quotient.mk v) ?_)
  have key : ∀ x ∈ W.baseChange K, (W.mkQ.baseChange K) x = 0 := by
    intro x hx
    rw [Submodule.baseChange_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hx
        change (W.mkQ.baseChange K) ((1 : K) ⊗ₜ[k] w) = 0
        rw [LinearMap.baseChange_tmul, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr
          hw, tmul_zero]
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul a x _ hx => rw [map_smul, hx, smul_zero]
  have := key _ h
  rw [LinearMap.baseChange_tmul] at this
  exact this

end LinAlg

end RM6Sol

theorem _root_.AlgebraicGeometry.ProjSpace.forall_H0_twist_exists_isHomogeneous_of_baseChange_field
    {k : Type u} [Field k] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsAffineHom ι]
    (K : Type u) [Field K] [Algebra k K] {Z' : Scheme.{u}}
    (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)) [IsAffineHom ι']
    (e : Z' ⟶ Z)
    (hpb : IsPullback e (ι' ≫ ProjSpace.π K n) (ι ≫ ProjSpace.π k n) (Spec.map (CommRingCat.ofHom
      (algebraMap k K))))
    (hcomp : e ≫ ι = ι' ≫ ProjSpace.map k K n) (d : ℕ)
    (hK : ∀ c ∈ (ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).H0 (ProjSpace.stdCoverPullback ι'),
        ∃ (F : MvPolynomial (Fin (n + 1)) K) (hF : F.IsHomogeneous d),
          ∀ (s : (ProjSpace.stdCoverPullback ι').Idx 0) (i : Fin (n + 1)),
            (c s).val i =
              ProjSpace.restrictFun
                  (inf_le_right : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart
                    ι' i ≤
                    ProjSpace.pullbackChart ι' i)
                  (ι'.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
                    (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
                (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })))) :
    ∀ c ∈ (ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).H0 (ProjSpace.stdCoverPullback ι),
        ∃ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
          ∀ (s : (ProjSpace.stdCoverPullback ι).Idx 0) (i : Fin (n + 1)),
            (c s).val i =
              ProjSpace.restrictFun
                  (inf_le_right : (ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart
                    ι i ≤
                    ProjSpace.pullbackChart ι i)
                  (ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
                    (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
                (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ }))) := by
  classical
  intro c hc
  obtain ⟨ε, hεd, hεval⟩ :=
    ProjSpace.exists_linearEquiv_baseChange_cochain_twist_of_isPullback ι K ι' e hpb hcomp d
  obtain ⟨Θ, hΘ⟩ := RM6Sol.exists_theta ι d
  obtain ⟨Θ', hΘ'⟩ := RM6Sol.exists_theta ι' d
  have hle : ∀ (s : (ProjSpace.stdCoverPullback ι).Idx 0) (j : Fin (n + 1)),
      (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' j ≤
        e ⁻¹ᵁ ((ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j) := by
    intro s j
    rw [← RM6Sol.preimage_inter ι K ι' e hcomp s, ← RM6Sol.preimage_pullbackChart ι K ι' e hcomp j]
    exact le_rfl
  have hle' : ∀ (s : (ProjSpace.stdCoverPullback ι).Idx 0) (j : Fin (n + 1)),
      (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' j ≤ e ⁻¹ᵁ
        ProjSpace.pullbackChart ι j := by
    intro s j
    rw [RM6Sol.preimage_pullbackChart ι K ι' e hcomp j]
    exact inf_le_right
  have hmapmem : ∀ F : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d),
      MvPolynomial.map (algebraMap k K) (F : MvPolynomial (Fin (n + 1)) k) ∈
        MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K d :=
    fun F => (MvPolynomial.mem_homogeneousSubmodule d _).mpr ((RM6Sol.isHomogeneous_of_mem d F).map
      _)
  have hnat : ∀ F : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d),
      ε 0 ((1 : K) ⊗ₜ[k] ((Θ F : ↥((ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).H0
        (ProjSpace.stdCoverPullback ι))) :
          (ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).cochain (ProjSpace.stdCoverPullback ι) 0)) =
        ((Θ' ⟨_, hmapmem F⟩ : ↥((ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).H0
          (ProjSpace.stdCoverPullback ι'))) :
          (ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).cochain (ProjSpace.stdCoverPullback ι') 0)
            := by
    intro F
    funext s
    refine ProjSpace.twistObj.ext (funext fun j => ?_)
    rw [hεval 0 _ s j (hle s j), hΘ F s j, hΘ' _ s j]
    unfold RM6Sol.chartVal ProjSpace.HomogeneousSectionsH0.chartVal
    refine (RM6Sol.restrictFun_app_eq e _ (hle s j) (hle' s j) _).trans ?_
    refine (RM6Sol.restrictFun_app_pullAway ι K ι' e hcomp j _ (hle' s j) inf_le_right).trans ?_
    rw [RM6Sol.toB_mkDeg K j d F.1 (RM6Sol.isHomogeneous_of_mem d F)]
  have hc' : ε 0 ((1 : K) ⊗ₜ[k] c) ∈
      (ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).H0 (ProjSpace.stdCoverPullback ι') := by
    rw [LinearMap.mem_ker]
    have h1 := LinearMap.congr_fun (hεd 0) ((1 : K) ⊗ₜ[k] c)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul] at h1
    rw [← h1, LinearMap.mem_ker.mp hc, tmul_zero, map_zero]
  obtain ⟨G, hG, hGform⟩ := hK _ hc'
  have hGmem : G ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K d :=
    (MvPolynomial.mem_homogeneousSubmodule d G).mpr hG
  have hcG : ε 0 ((1 : K) ⊗ₜ[k] c) =
      ((Θ' ⟨G, hGmem⟩ : ↥((ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).H0
        (ProjSpace.stdCoverPullback ι'))) :
        (ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).cochain (ProjSpace.stdCoverPullback ι') 0) :=
          by
    funext s
    refine ProjSpace.twistObj.ext (funext fun j => ?_)
    rw [hGform s j, hΘ' _ s j]
    rfl
  let W : Submodule k ((ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).cochain
    (ProjSpace.stdCoverPullback ι) 0) :=
    LinearMap.range (((ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).H0 (ProjSpace.stdCoverPullback
      ι)).subtype ∘ₗ Θ)
  have hmon : ∀ μ ∈ G.support, (MvPolynomial.monomial μ (1 : k)) ∈
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d := by
    intro μ hμ
    rw [MvPolynomial.mem_homogeneousSubmodule]
    have hdeg : μ.degree = d := by
      rw [Finsupp.degree_eq_weight_one]; exact hG (MvPolynomial.mem_support_iff.mp hμ)
    exact MvPolynomial.isHomogeneous_monomial _ hdeg
  have hGsum : (⟨G, hGmem⟩ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K d)) =
      ∑ μ ∈ G.support.attach, G.coeff μ.1 • ⟨MvPolynomial.map (algebraMap k K)
        (MvPolynomial.monomial μ.1 (1 : k)),
        hmapmem ⟨_, hmon μ.1 μ.2⟩⟩ := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul, MvPolynomial.map_monomial, map_one]
    conv_lhs => rw [G.as_sum]
    rw [← Finset.sum_attach]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  let M : Submodule K ((ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).cochain
    (ProjSpace.stdCoverPullback ι') 0) :=
    (W.baseChange K).map (ε 0).toLinearMap
  have hspan' : Θ' ⟨G, hGmem⟩ ∈
      M.comap ((ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).H0 (ProjSpace.stdCoverPullback
        ι')).subtype := by
    rw [hGsum, map_sum]
    refine Submodule.sum_mem _ fun μ _ => ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    rw [Submodule.mem_comap, Submodule.subtype_apply, ← hnat ⟨_, hmon μ.1 μ.2⟩]
    exact Submodule.mem_map_of_mem (Submodule.tmul_mem_baseChange_of_mem 1
      (LinearMap.mem_range.mpr ⟨⟨_, hmon μ.1 μ.2⟩, rfl⟩))
  have hspan : ((Θ' ⟨G, hGmem⟩ : ↥((ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).H0
    (ProjSpace.stdCoverPullback ι'))) :
        (ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).cochain (ProjSpace.stdCoverPullback ι') 0) ∈
      (W.baseChange K).map (ε 0).toLinearMap := hspan'
  have h1c : (1 : K) ⊗ₜ[k] c ∈ W.baseChange K := by
    obtain ⟨y, hy, hyeq⟩ := Submodule.mem_map.mp hspan
    have : y = (1 : K) ⊗ₜ[k] c := (ε 0).injective (hyeq.trans hcG.symm)
    rw [← this]; exact hy
  have hcW : c ∈ W := RM6Sol.mem_of_one_tmul_mem_baseChange K W c h1c
  obtain ⟨F, hF⟩ := LinearMap.mem_range.mp hcW
  refine ⟨F.1, RM6Sol.isHomogeneous_of_mem d F, fun s i => ?_⟩
  have := hΘ F s i
  rw [show ((Θ F : ↥((ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).H0 (ProjSpace.stdCoverPullback
    ι))) :
      (ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).cochain (ProjSpace.stdCoverPullback ι) 0) = c
        from hF] at this
  exact this
end ProjSpace_forall_H0_twist_exists_isHomogeneous_of_baseChange_field
end AlgebraicCurves.Geometry.Projective.Proofs
end ProofImplementation
