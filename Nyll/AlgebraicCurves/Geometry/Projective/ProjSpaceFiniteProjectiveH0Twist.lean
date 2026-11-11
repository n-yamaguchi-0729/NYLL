/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback.lean
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
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Nyll.SchemeTheory.ProjectiveSpace.Basic
public import Nyll.SchemeTheory.ProjectiveSpace.Cover
public import Nyll.AlgebraicCurves.Geometry.Projective.ProjTwistDatum
public import Nyll.AlgebraicCurves.Hilbert.Functor.Basic
public import Nyll.AlgebraicCurves.Geometry.Schemes.Covers.OrderedAffineCoverComap
public import Nyll.SchemeTheory.ProjectiveSpace.StandardChartsBaseChange
public import Nyll.AlgebraicCurves.Cohomology.Sheaves.BaseChange.ProjSpaceLinearEquivBaseChangeCochainTwist
public import Nyll.AlgebraicCurves.Geometry.Projective.ProjSpaceLinearMapHomogeneousSubmoduleTwistObjTopValEq

/-!
# Proj Space finite projective H0 twist of ker base Change of is Pullback
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Projective.Proofs
namespace ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct
  AlgebraicGeometry.HilbertFunctor

attribute [local instance] MvPolynomial.gradedAlgebra

open HomogeneousLocalization

namespace K4ISol

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

variable {n : ℕ} {k : Type u} [CommRing k] {Zk : Scheme.{u}}
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

section KerEquiv

theorem exists_kerEquiv {R : Type*} [CommRing R] {M M' N N' : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N']
    (e₀ : M ≃ₗ[R] M') {e₁ : N ≃ₗ[R] N'} (f : M →ₗ[R] N) (f' : M' →ₗ[R] N')
    (h : e₁.toLinearMap ∘ₗ f = f' ∘ₗ e₀.toLinearMap) :
    ∃ η : LinearMap.ker f ≃ₗ[R] LinearMap.ker f', ∀ x : LinearMap.ker f, (η x : M') = e₀ (x : M) :=
      by
  have hk : LinearMap.ker f = (LinearMap.ker f').comap (e₀ : M →ₗ[R] M') := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_comap, LinearEquiv.coe_coe]
    have h1 := LinearMap.congr_fun h x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h1
    rw [← h1, LinearEquiv.map_eq_zero_iff]
  refine ⟨(LinearEquiv.ofEq _ _ hk).trans (LinearEquiv.ofSubmodule' e₀ (LinearMap.ker f')), fun x
    => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.ofSubmodule'_apply, LinearEquiv.coe_ofEq_apply]

end KerEquiv

end K4ISol

theorem
  _root_.AlgebraicGeometry.ProjSpace.finite_projective_H0_twist_of_ker_baseChange_of_isPullback
    {A₀ : Type u} [CommRing A₀] {n : ℕ} {Z₀ : Scheme.{u}}
    (ι₀ : Z₀ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A₀)) [IsClosedImmersion ι₀]
    (A : Type u) [CommRing A] [Algebra A₀ A] {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsClosedImmersion ι]
    (g : Z ⟶ Z₀)
    (hpb : IsPullback g (ι ≫ ProjSpace.π A n) (ι₀ ≫ ProjSpace.π A₀ n) (Spec.map (CommRingCat.ofHom
      (algebraMap A₀ A))))
    (hcomp : g ≫ ι₀ = ι ≫ ProjSpace.map A₀ A n) (d : ℕ)
    (Θ₀ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A₀ d) →ₗ[A₀] (ProjSpace.twist (ι₀ ≫
      ProjSpace.π A₀ n) ι₀ d).cochain (ProjSpace.stdCoverPullback ι₀) 0)
    (hΘ₀ : ∀ (F : MvPolynomial (Fin (n + 1)) A₀) (hF : F.IsHomogeneous d) (s :
      (ProjSpace.stdCoverPullback ι₀).Idx 0) (i : Fin (n + 1)),
      (Θ₀ ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ s).val i =
        ProjSpace.restrictFun
          (inf_le_right : (ProjSpace.stdCoverPullback ι₀).inter s ⊓ ProjSpace.pullbackChart ι₀ i ≤
            ProjSpace.pullbackChart ι₀ i)
          ((ι₀.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A₀)
            (MvPolynomial.X i)))
                (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A₀)
                  (MvPolynomial.X i)
                  (HomogeneousLocalization.mk
                    { deg := d
                      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                      den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                        (MvPolynomial.isHomogeneous_X_pow i d)⟩
                      den_mem := ⟨d, rfl⟩ }))))
    (r : ℕ)
    (hfin : Module.Finite A (LinearMap.ker (((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d
      (ProjSpace.stdCoverPullback ι₀) 0).baseChange A)))
    (hproj : Module.Projective A (LinearMap.ker (((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d
      (ProjSpace.stdCoverPullback ι₀) 0).baseChange A)))
    (hrank : ∀ 𝔮 : PrimeSpectrum A,
      Module.rankAtStalk (LinearMap.ker (((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d
        (ProjSpace.stdCoverPullback ι₀) 0).baseChange A)) 𝔮 = r)
    (hgen : LinearMap.ker (((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d
      (ProjSpace.stdCoverPullback ι₀) 0).baseChange A) ≤ LinearMap.range (Θ₀.baseChange A)) :
    Module.Finite A ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).H0 (ProjSpace.stdCoverPullback ι))
      ∧
    Module.Projective A ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).H0 (ProjSpace.stdCoverPullback
      ι)) ∧
    (∀ 𝔮 : PrimeSpectrum A, Module.rankAtStalk (↥((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).H0
      (ProjSpace.stdCoverPullback ι))) 𝔮 = r) ∧
    (∀ c ∈ (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).H0 (ProjSpace.stdCoverPullback ι),
      ∃ (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d),
        ∀ (s : (ProjSpace.stdCoverPullback ι).Idx 0) (i : Fin (n + 1)),
          (c s).val i =
            ProjSpace.restrictFun
              (inf_le_right : (ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι i
                ≤ ProjSpace.pullbackChart ι i)
              ((ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
                (MvPolynomial.X i)))
                (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
                  (MvPolynomial.X i)
                  (HomogeneousLocalization.mk
                    { deg := d
                      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                      den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                        (MvPolynomial.isHomogeneous_X_pow i d)⟩
                      den_mem := ⟨d, rfl⟩ })))) := by
  classical
  obtain ⟨ε, hεd, hεval⟩ :=
    ProjSpace.exists_linearEquiv_baseChange_cochain_twist_of_isPullback ι₀ A ι g hpb hcomp d
  obtain ⟨Θ, hΘ⟩ := K4ISol.exists_theta ι d
  obtain ⟨η, hη⟩ := K4ISol.exists_kerEquiv (ε 0)
    (((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀)
      0).baseChange A)
    ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).d (ProjSpace.stdCoverPullback ι) 0) (hεd 0)
  have := hfin
  have := hproj
  refine ⟨Module.Finite.equiv η, Module.Projective.of_equiv η,
    fun 𝔮 => (congrFun (Module.rankAtStalk_eq_of_equiv η) 𝔮).symm.trans (hrank 𝔮), ?_⟩
  have hle : ∀ (s : (ProjSpace.stdCoverPullback ι₀).Idx 0) (j : Fin (n + 1)),
      (ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j ≤
        g ⁻¹ᵁ ((ProjSpace.stdCoverPullback ι₀).inter s ⊓ ProjSpace.pullbackChart ι₀ j) := by
    intro s j
    rw [← K4ISol.preimage_inter ι₀ A ι g hcomp s, ← K4ISol.preimage_pullbackChart ι₀ A ι g hcomp j]
    exact le_rfl
  have hle' : ∀ (s : (ProjSpace.stdCoverPullback ι₀).Idx 0) (j : Fin (n + 1)),
      (ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j ≤ g ⁻¹ᵁ
        ProjSpace.pullbackChart ι₀ j := by
    intro s j
    rw [K4ISol.preimage_pullbackChart ι₀ A ι g hcomp j]
    exact inf_le_right
  have hmapmem : ∀ G : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A₀ d),
      MvPolynomial.map (algebraMap A₀ A) (G : MvPolynomial (Fin (n + 1)) A₀) ∈
        MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A d :=
    fun G => (MvPolynomial.mem_homogeneousSubmodule d _).mpr ((K4ISol.isHomogeneous_of_mem d G).map
      _)
  have hnat : ∀ G : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A₀ d),
      ε 0 ((1 : A) ⊗ₜ[A₀] Θ₀ G) =
        ((Θ ⟨_, hmapmem G⟩ : ↥((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).H0
          (ProjSpace.stdCoverPullback ι))) :
          (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain (ProjSpace.stdCoverPullback ι) 0) :=
            by
    intro G
    funext s
    refine ProjSpace.twistObj.ext (funext fun j => ?_)
    rw [hεval 0 _ s j (hle s j)]
    have h0 := hΘ₀ G.1 (K4ISol.isHomogeneous_of_mem d G) s j
    rw [show (⟨G.1, (MvPolynomial.mem_homogeneousSubmodule d G.1).mpr (K4ISol.isHomogeneous_of_mem
      d G)⟩ :
        ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A₀ d)) = G from Subtype.ext rfl] at h0
    rw [h0, hΘ _ s j]
    unfold K4ISol.chartVal ProjSpace.HomogeneousSectionsH0.chartVal
    refine (K4ISol.restrictFun_app_eq g _ (hle s j) (hle' s j) _).trans ?_
    refine (K4ISol.restrictFun_app_pullAway ι₀ A ι g hcomp j _ (hle' s j) inf_le_right).trans ?_
    rw [K4ISol.toB_mkDeg A j d G.1 (K4ISol.isHomogeneous_of_mem d G)]
  let W : Submodule A ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain
    (ProjSpace.stdCoverPullback ι) 0) :=
    LinearMap.range (((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).H0 (ProjSpace.stdCoverPullback
      ι)).subtype ∘ₗ Θ)
  have key : ∀ y : A ⊗[A₀] ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A₀ d),
      ε 0 (Θ₀.baseChange A y) ∈ W := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul a G =>
        have ha : a ⊗ₜ[A₀] (Θ₀ G) = a • ((1 : A) ⊗ₜ[A₀] Θ₀ G) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [LinearMap.baseChange_tmul, ha, map_smul]
        refine W.smul_mem a ?_
        rw [hnat G]
        exact LinearMap.mem_range.mpr ⟨⟨_, hmapmem G⟩, rfl⟩
    | add x y hx hy => rw [map_add, map_add]; exact W.add_mem hx hy
  intro c hc
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (hgen (η.symm ⟨c, hc⟩).2)
  have hc_eq : ε 0 (Θ₀.baseChange A y) = c := by
    rw [hy, ← hη, LinearEquiv.apply_symm_apply]
  have hcW : c ∈ W := hc_eq ▸ key y
  obtain ⟨F, hF⟩ := LinearMap.mem_range.mp hcW
  refine ⟨F.1, K4ISol.isHomogeneous_of_mem d F, fun s i => ?_⟩
  have := hΘ F s i
  rw [show ((Θ F : ↥((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).H0 (ProjSpace.stdCoverPullback
    ι))) :
      (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain (ProjSpace.stdCoverPullback ι) 0) = c
        from hF] at this
  exact this
end ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback
end AlgebraicCurves.Geometry.Projective.Proofs
end ProofImplementation
