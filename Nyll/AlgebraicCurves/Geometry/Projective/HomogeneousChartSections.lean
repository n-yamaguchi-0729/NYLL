/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

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

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.NormCast
public import Nyll.SchemeTheory.ProjectiveSpace.Basic
public import Nyll.SchemeTheory.ProjectiveSpace.Cover
public import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
public import Nyll.AlgebraicCurves.Geometry.Projective.ProjTwistDatum

/-!
# Homogeneous fractions on projective coordinate charts

The formulas retain the original homogeneous-localization elements and chart
restriction maps. Scalar compatibility uses the algebra induced by the same
structure morphism. Closed-immersion assumptions are local to the two lemmas
that use surjectivity or affine localization.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjSpace.HomogeneousChartSections

/-- The projective structure map sends a scalar to its actual chart-localization image. -/
theorem map_appTop_π_eq_awayToSection_algebraMap (k : Type u) [CommRing k] (n : ℕ) (i : Fin (n +
  1)) (r : k) :
    (Proj (homogeneousSubmodule (Fin (n + 1)) k)).presheaf.map
        (homOfLE (le_top : Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) k) (X i) ≤ ⊤)).op
        ((ProjSpace.π k n).appTop ((Scheme.ΓSpecIso (.of k)).inv r))
      = Proj.awayToSection (homogeneousSubmodule (Fin (n + 1)) k) (X i)
          (algebraMap k (Away (homogeneousSubmodule (Fin (n + 1)) k) (X i)) r) := by
  let 𝒜 := homogeneousSubmodule (Fin (n + 1)) k
  let P := Proj 𝒜
  let D : P.Opens := Proj.basicOpen 𝒜 (X i)
  let e := Proj.basicOpenIsoSpec 𝒜 (X i) (ProjSpace.X_mem_one k n i) one_pos
  let x : Γ(Spec (.of k), ⊤) := (Scheme.ΓSpecIso (.of k)).inv r
  let am := algebraMap k (Away 𝒜 (X i))
  have h1 : (Proj.awayι 𝒜 (X i) (ProjSpace.X_mem_one k n i) one_pos).appTop ((ProjSpace.π k
    n).appTop x)
      = (Scheme.ΓSpecIso (.of (Away 𝒜 (X i)))).inv (am r) := by
    have h := ProjSpace.awayι_comp_π k n i
    have h' : ((ProjSpace.π k n).appTop ≫ (Proj.awayι 𝒜 (X i) (ProjSpace.X_mem_one k n i)
      one_pos).appTop) x
        = (Spec.map (CommRingCat.ofHom am)).appTop x := by
      rw [← Scheme.Hom.comp_appTop, h]
    rw [CommRingCat.comp_apply] at h'
    rw [h']
    have nat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom am)
    have nat' : ((CommRingCat.ofHom am) ≫ (Scheme.ΓSpecIso (.of (Away 𝒜 (X i)))).inv) r
        = ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec.map (CommRingCat.ofHom am)).appTop) r :=
          by rw [nat]
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at nat'
    exact nat'.symm
  have h2 : ∀ y : Γ(P, ⊤), (Proj.awayι 𝒜 (X i) (ProjSpace.X_mem_one k n i) one_pos).appTop y
      = e.inv.appTop (D.topIso.inv (P.presheaf.map (homOfLE (le_top : D ≤ ⊤)).op y)) := by
    intro y
    rw [← Proj.basicOpenIsoSpec_inv_ι, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      Scheme.Opens.ι_appTop,
      Scheme.Opens.topIso_inv]
    congr 1
  have h3 : ∀ z : Γ(Spec (.of (Away 𝒜 (X i))), ⊤),
      e.hom.appTop z = D.topIso.inv (Proj.awayToSection 𝒜 (X i) ((Scheme.ΓSpecIso (.of (Away 𝒜 (X
        i)))).hom z)) := by
    intro z
    have := Proj.basicOpenToSpec_app_top 𝒜 (X i)
    rw [Proj.basicOpenIsoSpec_hom]
    change (Proj.basicOpenToSpec 𝒜 (X i)).app ⊤ z = _
    rw [this]
    rfl
  have h4 : ∀ w : Γ(↑D, ⊤), e.hom.appTop (e.inv.appTop w) = w := by
    intro w
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
    rfl
  have key : D.topIso.inv ((Proj (homogeneousSubmodule (Fin (n + 1)) k)).presheaf.map
        (homOfLE (le_top : Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) k) (X i) ≤ ⊤)).op
        ((ProjSpace.π k n).appTop ((Scheme.ΓSpecIso (.of k)).inv r)))
      = D.topIso.inv (Proj.awayToSection 𝒜 (X i) (am r)) := by
    have hx := h2 ((ProjSpace.π k n).appTop x)
    rw [h1] at hx
    have := congrArg (fun w => e.hom.appTop w) hx
    simp only [h4] at this
    rw [← this, h3]
    congr 2
    exact CategoryTheory.Iso.inv_hom_id_apply (Scheme.ΓSpecIso (.of (Away 𝒜 (X i)))) (am r)
  have hinj : Function.Injective (fun w => D.topIso.inv w) := fun a b hab => by
    have := congrArg (fun w => D.topIso.hom w) hab
    simpa only [CategoryTheory.Iso.inv_hom_id_apply] using this
  exact hinj key

section Frac

variable {k : Type u} [CommRing k] {n : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

/-- The original homogeneous numerator divided by a matching power of the chosen coordinate. -/
noncomputable def frac (d : ℕ) (p : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) (i :
  Fin (n + 1)) : Away 𝒜 (X i) :=
  HomogeneousLocalization.mk
    { deg := d
      num := ⟨p.1, p.2⟩
      den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
        (MvPolynomial.isHomogeneous_X_pow i d)⟩
      den_mem := ⟨d, rfl⟩ }

/-- The underlying localization value of the specified homogeneous fraction. -/
theorem val_frac (d : ℕ) (p : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) (i : Fin (n +
  1)) :
    (frac d p i).val = Localization.mk p.1 (⟨MvPolynomial.X i ^ d, ⟨d, rfl⟩⟩ : Submonoid.powers
      (MvPolynomial.X i)) := rfl

/-- Addition of homogeneous numerators agrees with addition of their chart fractions. -/
theorem frac_add (d : ℕ) (p q : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) (i : Fin (n
  + 1)) :
    frac d (p + q) i = frac d p i + frac d q i := by
  apply HomogeneousLocalization.val_injective
  rw [val_add, val_frac, val_frac, val_frac, Localization.add_mk_self]
  rfl

/-- Scalar multiplication agrees with the original localization algebra map. -/
theorem frac_smul (d : ℕ) (c : k) (p : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) (i :
  Fin (n + 1)) :
    frac d (c • p) i = algebraMap k (Away 𝒜 (X i)) c * frac d p i := by
  apply HomogeneousLocalization.val_injective
  rw [val_mul, val_frac, val_frac, ProjSpace.val_algebraMap, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul, one_mul]
  congr 1
  rw [Submodule.coe_smul, MvPolynomial.smul_eq_C_mul]

/-- The two chart fractions agree after the original ratio transition. -/
theorem awayMap_frac_eq (d : ℕ) (p : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) (i j :
  Fin (n + 1)) :
    awayMap 𝒜 (ProjSpace.X_mem_one k n j) rfl (frac d p i)
      = awayMap 𝒜 (ProjSpace.X_mem_one k n j) rfl (ProjSpace.ratio k n i j) ^ d
          * awayMap 𝒜 (ProjSpace.X_mem_one k n i)
              (mul_comm (X i) (X j) : (X i * X j : MvPolynomial (Fin (n + 1)) k) = X j * X i) (frac
                d p j) := by
  apply HomogeneousLocalization.val_injective
  rw [val_mul, val_pow]
  rw [frac, val_awayMap_mk, frac, val_awayMap_mk,
    ProjSpace.val_awayMap_ratio k n i j j (ProjSpace.X_mem_one k n j) rfl _ (X j)
      (by rw [ProjSpace.ratio, Away.val_mk]),
    Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow]
  ring

end Frac

section Comp

variable {k : Type u} [CommRing k] {n : ℕ} {Z : Scheme.{u}}
  (φ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

/-- The actual chart section obtained from a homogeneous-localization element. -/
noncomputable def pullAway (i : Fin (n + 1)) (a : Away 𝒜 (X i)) : Γ(Z, ProjSpace.pullbackChart φ i)
  :=
  (φ.app (Proj.basicOpen 𝒜 (X i))).hom ((Proj.awayToSection 𝒜 (X i)).hom a)

/-- The chart section is the composite of the specified two ring homomorphisms. -/
theorem pullAway_eq (i : Fin (n + 1)) (a : Away 𝒜 (X i)) :
    pullAway φ i a = (φ.app (Proj.basicOpen 𝒜 (X i))) (Proj.awayToSection 𝒜 (X i) a) := rfl

/-- The chart-section map preserves addition. -/
theorem pullAway_add (i : Fin (n + 1)) (a b : Away 𝒜 (X i)) :
    pullAway φ i (a + b) = pullAway φ i a + pullAway φ i b :=
  map_add ((φ.app (Proj.basicOpen 𝒜 (X i))).hom.comp (Proj.awayToSection 𝒜 (X i)).hom) a b

/-- The chart-section map preserves multiplication. -/
theorem pullAway_mul (i : Fin (n + 1)) (a b : Away 𝒜 (X i)) :
    pullAway φ i (a * b) = pullAway φ i a * pullAway φ i b :=
  map_mul ((φ.app (Proj.basicOpen 𝒜 (X i))).hom.comp (Proj.awayToSection 𝒜 (X i)).hom) a b

/-- The chart-section map preserves zero. -/
theorem pullAway_zero (i : Fin (n + 1)) : pullAway φ i 0 = 0 :=
  map_zero ((φ.app (Proj.basicOpen 𝒜 (X i))).hom.comp (Proj.awayToSection 𝒜 (X i)).hom)

/-- Restricting the first chart section uses the left localization map. -/
theorem restrictFun_pullAway_left (i j : Fin (n + 1)) (a : Away 𝒜 (X i)) :
    ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left φ i j) (pullAway φ i a)
      = (φ.app (Proj.basicOpen 𝒜 (X i * X j))).hom
          ((Proj.awayToSection 𝒜 (X i * X j)).hom (awayMap 𝒜 (ProjSpace.X_mem_one k n j) rfl a)) :=
            by
  have h1 := congrArg (fun (ψ : CommRingCat.of (Away 𝒜 (X i)) ⟶ _) => ψ.hom a)
    (Proj.awayMap_awayToSection 𝒜 (ProjSpace.X_mem_one k n j)
      (rfl : (X i * X j : MvPolynomial (Fin (n + 1)) k) = X i * X j))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
  rw [h1]
  have h2 := congrArg (fun ψ => ψ.hom ((Proj.awayToSection 𝒜 (X i)).hom a))
    (φ.naturality (homOfLE (show Proj.basicOpen 𝒜 (X i * X j) ≤ Proj.basicOpen 𝒜 (X i) from by
      rw [Proj.basicOpen_mul]; exact inf_le_left)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  rw [h2]
  rfl

/-- Restricting the second chart section uses the right localization map. -/
theorem restrictFun_pullAway_right (i j : Fin (n + 1)) (a : Away 𝒜 (X j)) :
    ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_right φ i j) (pullAway φ j a)
      = (φ.app (Proj.basicOpen 𝒜 (X i * X j))).hom
          ((Proj.awayToSection 𝒜 (X i * X j)).hom (awayMap 𝒜 (ProjSpace.X_mem_one k n i)
            (mul_comm (X i) (X j) : (X i * X j : MvPolynomial (Fin (n + 1)) k) = X j * X i) a)) :=
              by
  have h1 := congrArg (fun (ψ : CommRingCat.of (Away 𝒜 (X j)) ⟶ _) => ψ.hom a)
    (Proj.awayMap_awayToSection 𝒜 (ProjSpace.X_mem_one k n i)
      (mul_comm (X i) (X j) : (X i * X j : MvPolynomial (Fin (n + 1)) k) = X j * X i))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
  rw [h1]
  have h2 := congrArg (fun ψ => ψ.hom ((Proj.awayToSection 𝒜 (X j)).hom a))
    (φ.naturality (homOfLE (show Proj.basicOpen 𝒜 (X i * X j) ≤ Proj.basicOpen 𝒜 (X j) from by
      rw [Proj.basicOpen_mul]; exact inf_le_right)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  rw [h2]
  rfl

/-- The homogeneous chart fractions satisfy the twist transition formula. -/
theorem restrictFun_pullAway_frac (d : ℕ) (p : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k
  d)) (i j : Fin (n + 1)) :
    ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left φ i j) (pullAway φ i (frac d p i))
      = ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left φ i j) (ProjSpace.frameUnit φ i j)
        ^ d
          * ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_right φ i j) (pullAway φ j (frac d
            p j)) := by
  rw [restrictFun_pullAway_left, restrictFun_pullAway_right, ProjSpace.restrictFun_frameUnit_left]
  let f := (φ.app (Proj.basicOpen 𝒜 (X i * X j))).hom.comp (Proj.awayToSection 𝒜 (X i * X j)).hom
  have hf : ∀ a, f a = (φ.app (Proj.basicOpen 𝒜 (X i * X j))).hom ((Proj.awayToSection 𝒜 (X i * X
    j)).hom a) :=
    fun _ => rfl
  rw [← hf, ← hf, ← hf, awayMap_frac_eq, map_mul, map_pow]
  rfl

/-- The restricted scalar section uses the same structure-morphism algebra. -/
theorem pullAway_algebraMap (i : Fin (n + 1)) (c : k) {W : Z.Opens} (hW : W ≤
  ProjSpace.pullbackChart φ i) :
    ProjSpace.restrictFun hW (pullAway φ i (algebraMap k (Away 𝒜 (X i)) c))
      = (Scheme.TwoAffineOpenCover.algebraOfHom (φ ≫ ProjSpace.π k n) W).algebraMap c := by
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
  erw [Scheme.Hom.comp_appLE φ (ProjSpace.π k n) ⊤ W le_top]
  rw [CommRingCat.comp_apply]
  change _ = (φ.appLE ⊤ W _) ((ProjSpace.π k n).appTop ((Scheme.ΓSpecIso (.of k)).inv c))
  rw [pullAway, ← map_appTop_π_eq_awayToSection_algebraMap k n i c]
  have : φ.appLE ⊤ W (hW.trans (le_top.trans (Scheme.Hom.preimage_top φ).ge)) =
      (Proj 𝒜).presheaf.map (homOfLE (le_top : Proj.basicOpen 𝒜 (X i) ≤ ⊤)).op ≫
        φ.appLE (Proj.basicOpen 𝒜 (X i)) W hW := by
    exact (φ.map_appLE hW
      (homOfLE (le_top : Proj.basicOpen 𝒜 (X i) ≤ ⊤)).op).symm
  erw [this, CommRingCat.comp_apply]

end Comp

section Main

variable {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
  (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

/-- The transition section is the image of the original coordinate ratio. -/
theorem frameUnit_eq_pullAway (i j : Fin (n + 1)) :
    ProjSpace.frameUnit ι i j = pullAway ι i (ProjSpace.ratio A n i j) := rfl

/-- A power of the graded coordinate action has the stated component formula. -/
theorem xMul_pow_apply (j : Fin (n + 1)) (k : ℕ) (f : ProjSpace.twistFam (ι ≫ ProjSpace.π A n) ι)
  (d : ℤ) (i : Fin (n + 1)) :
    (((ProjSpace.twistGradedModule ι (ι ≫ ProjSpace.π A n)).xMul j ^ k) f) d i =
      ProjSpace.restrictFun (inf_le_right : (⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart ι i ≤
        ProjSpace.pullbackChart ι i)
        (ProjSpace.frameUnit ι i j) ^ k * f (d - k) i := by
  induction k generalizing d with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, sub_zero, one_mul]
    rfl
  | succ k ih =>
    erw [pow_succ', Module.End.mul_apply]
    change ProjSpace.restrictFun (inf_le_right : (⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart ι i ≤
      ProjSpace.pullbackChart ι i)
        (ProjSpace.frameUnit ι i j) *
      (((ProjSpace.twistGradedModule ι (ι ≫ ProjSpace.π A n)).xMul j ^ k) f) (d - 1) i = _
    erw [ih, ← mul_assoc, ← pow_succ']
    congr 2
    push_cast
    ring

/-- A closed immersion gives a homogeneous-fraction presentation on a chart. -/
theorem exists_eq_pullAway_mk [IsClosedImmersion ι] (j : Fin (n + 1)) (z : Γ(Z,
  ProjSpace.pullbackChart ι j)) :
    ∃ (a : ℕ) (G : MvPolynomial (Fin (n + 1)) A) (hG : G ∈ 𝒜 a),
      z = pullAway ι j (Away.mk 𝒜 (ProjSpace.X_mem_one A n j) a G (by simpa using hG)) := by
  have hsurjι : Function.Surjective (ι.app (Proj.basicOpen 𝒜 (X j))) :=
    ι.app_surjective _ (Proj.isAffineOpen_basicOpen 𝒜 (X j) (ProjSpace.X_mem_one A n j) one_pos)
  have hsurjA : Function.Surjective (Proj.awayToSection 𝒜 (X j)).hom := by
    let e := Proj.basicOpenIsoAway 𝒜 (X j) (ProjSpace.X_mem_one A n j) one_pos
    intro s
    refine ⟨e.inv.hom s, ?_⟩
    change (e.inv ≫ e.hom).hom s = s
    rw [e.inv_hom_id]
    rfl
  obtain ⟨s, rfl⟩ := hsurjι z
  obtain ⟨q, rfl⟩ := hsurjA s
  obtain ⟨a, G, hG', rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 (ProjSpace.X_mem_one A n
    j) q
  exact ⟨a, G, by simpa using hG', rfl⟩

/-- The nonvanishing open of a coordinate ratio lies in the other chart. -/
theorem basicOpen_frameUnit_le (i j : Fin (n + 1)) :
    Z.basicOpen (ProjSpace.frameUnit ι i j) ≤ ProjSpace.pullbackChart ι j := by
  have hXi := ProjSpace.X_mem_one A n i
  have hXj := ProjSpace.X_mem_one A n j
  let D : (Proj 𝒜).Opens := Proj.basicOpen 𝒜 (X i)
  let s : Γ(Proj 𝒜, D) := (Proj.awayToSection 𝒜 (X i)).hom (ProjSpace.ratio A n i j)
  have h1 : Z.basicOpen (ProjSpace.frameUnit ι i j) = ι ⁻¹ᵁ (Proj 𝒜).basicOpen s :=
    (Scheme.preimage_basicOpen ι s).symm
  rw [h1]
  suffices hP : (Proj 𝒜).basicOpen s ≤ Proj.basicOpen 𝒜 (X j) from fun x hx => hP hx
  let e := Proj.basicOpenIsoSpec 𝒜 (X i) hXi one_pos
  have ht : ProjSpace.ratio A n i j = Away.isLocalizationElem hXi hXj := by
    apply HomogeneousLocalization.val_injective
    simp only [ProjSpace.ratio, Away.isLocalizationElem, HomogeneousLocalization.Away.val_mk,
      pow_one]
  have ha : Proj.awayι 𝒜 (X i) hXi one_pos ⁻¹ᵁ Proj.basicOpen 𝒜 (X j) =
      PrimeSpectrum.basicOpen (Away.isLocalizationElem hXi hXj) :=
    Proj.awayι_preimage_basicOpen 𝒜 hXi one_pos hXj one_pos
  have hb : D.ι ⁻¹ᵁ Proj.basicOpen 𝒜 (X j) = e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen
    (Away.isLocalizationElem hXi hXj) := by
    rw [← ha, ← Proj.basicOpenIsoSpec_inv_ι, Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
      e.hom_inv_id]
    rfl
  have hc : D.ι ⁻¹ᵁ (Proj 𝒜).basicOpen s = e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (ProjSpace.ratio A n i
    j) := by
    rw [← Scheme.Opens.toSpecΓ_preimage_basicOpen]
    change D.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen s =
      (Proj.basicOpenIsoSpec 𝒜 (X i) hXi one_pos).hom ⁻¹ᵁ PrimeSpectrum.basicOpen (ProjSpace.ratio
        A n i j)
    rw [Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec]
    exact (Scheme.Hom.comp_preimage
      (Proj.basicOpen 𝒜 (X i)).toSpecΓ (Spec.map (Proj.awayToSection 𝒜 (X i)))
      (PrimeSpectrum.basicOpen (ProjSpace.ratio A n i j))).symm
  intro y hy
  have hyD : y ∈ D := (Proj 𝒜).basicOpen_le s hy
  have : (⟨y, hyD⟩ : D.toScheme) ∈ D.ι ⁻¹ᵁ (Proj 𝒜).basicOpen s := by
    change D.ι.base ⟨y, hyD⟩ ∈ (Proj 𝒜).basicOpen s
    simpa using hy
  rw [hc, ht, ← hb] at this
  simp only [Proj.mem_basicOpen] at this ⊢
  exact this

/-- A vanishing overlap section is killed by a power of the transition. -/
theorem exists_pow_mul_eq_zero [IsClosedImmersion ι] (i j : Fin (n + 1)) (δ : Γ(Z,
  ProjSpace.pullbackChart ι i))
    (hδ : ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left ι i j) δ = 0) :
    ∃ N : ℕ, ProjSpace.frameUnit ι i j ^ N * δ = 0 := by
  have hU : IsAffineOpen (ProjSpace.pullbackChart ι i) := ProjSpace.isAffineOpen_pullbackChart ι i
  set u := ProjSpace.frameUnit ι i j with hu
  have := hU.isLocalization_basicOpen u
  have hle : Z.basicOpen u ≤ ProjSpace.pullbackOverlap ι i j := by
    rw [ProjSpace.pullbackOverlap_eq_inf]
    exact le_inf (Z.basicOpen_le u) (basicOpen_frameUnit_le ι i j)
  have h0 : algebraMap Γ(Z, ProjSpace.pullbackChart ι i) Γ(Z, Z.basicOpen u) δ = 0 := by
    have : algebraMap Γ(Z, ProjSpace.pullbackChart ι i) Γ(Z, Z.basicOpen u) δ =
        ProjSpace.restrictFun hle (ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left ι i j)
          δ) := by
      rw [ProjSpace.restrictFun_restrictFun]; rfl
    rw [this, hδ, map_zero]
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers u) _ δ).mp h0
  exact ⟨N, hN⟩

/-- The chart-section map preserves powers. -/
theorem pullAway_pow (i : Fin (n + 1)) (a : Away 𝒜 (X i)) (N : ℕ) :
    pullAway ι i (a ^ N) = pullAway ι i a ^ N :=
  map_pow ((ι.app (Proj.basicOpen 𝒜 (X i))).hom.comp (Proj.awayToSection 𝒜 (X i)).hom) a N

/-- Transport of the degree leaves the same homogeneous fraction. -/
theorem frac_congr {d₁ d₂ : ℕ} (h : d₁ = d₂) (p : ↥(𝒜 d₁)) (i : Fin (n + 1)) :
    frac d₁ p i = frac d₂ ⟨p.1, h ▸ p.2⟩ i := by
  subst h; rfl

/-- Multiplying by a transition power shifts the actual numerator. -/
theorem frameUnit_pow_mul_pullAway_frac (i j : Fin (n + 1)) (N d : ℕ) (p : ↥(𝒜 d)) :
    ProjSpace.frameUnit ι i j ^ N * pullAway ι i (frac d p i) =
      pullAway ι i (frac (d + N) ⟨X j ^ N * p.1, by
        have h := SetLike.mul_mem_graded (SetLike.pow_mem_graded N (ProjSpace.X_mem_one A n j)) p.2
        rwa [smul_eq_mul, mul_one, Nat.add_comm N d] at h⟩ i) := by
  rw [frameUnit_eq_pullAway, ← pullAway_pow, ← pullAway_mul]
  congr 1
  apply HomogeneousLocalization.val_injective
  rw [val_mul, val_pow, ProjSpace.ratio, HomogeneousLocalization.Away.val_mk, val_frac, val_frac,
    Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow]
  ring

end Main

end AlgebraicGeometry.ProjSpace.HomogeneousChartSections
