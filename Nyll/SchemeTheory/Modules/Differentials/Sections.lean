/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Tactic.Choose
public import Nyll.SchemeTheory.RingTheory.Differentials.Basic
public import Nyll.SchemeTheory.Modules.ExteriorPower.Det
public import Nyll.SchemeTheory.Modules.ExteriorPower.PresheafExteriorPower
public import Nyll.SchemeTheory.Modules.KaehlerDifferentials
public import Nyll.SchemeTheory.Modules.Sections.SectionsAlgebra

/-!
# Sections of differential modules and exterior powers on affine opens
-/

@[expose] public section

attribute [local instance] AlgebraicGeometry.Scheme.Hom.kaehlerPresheafModule

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_kaehlerToSections_bijective_of_isAffineOpen.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace AffineDifferentialSections
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace KaehlerSections

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

/-- Restriction in the presheaf of Kähler differentials. -/
noncomputable abbrev pmap {W W' : X.Opens} (i : W' ≤ W) (w : (f.kaehlerPresheaf.obj (op W) : Type
    u)) :
    (f.kaehlerPresheaf.obj (op W') : Type u) :=
  (f.kaehlerPresheaf.map (homOfLE i).op).hom w

/-- Restriction of sections of the sheaf of Kähler differentials. -/
noncomputable abbrev res {W' W : X.Opens} (i : W' ≤ W) (s : (Γ(f.kaehler, W) : Type u)) :
    (Γ(f.kaehler, W') : Type u) :=
  f.kaehler.val.presheaf.map (homOfLE i).op s

lemma pmap_pmap {W₁ W₂ W₃ : X.Opens} (h₂₁ : W₂ ≤ W₁) (h₃₂ : W₃ ≤ W₂)
    (w : (f.kaehlerPresheaf.obj (op W₁) : Type u)) :
    pmap f h₃₂ (pmap f h₂₁ w) = pmap f (h₃₂.trans h₂₁) w := by
  change _ = (f.kaehlerPresheaf.map ((homOfLE h₂₁).op ≫ (homOfLE h₃₂).op)).hom w
  rw [PresheafOfModules.map_comp_apply]

lemma res_res {W₁ W₂ W₃ : X.Opens} (h₂₁ : W₂ ≤ W₁) (h₃₂ : W₃ ≤ W₂) (s : (Γ(f.kaehler, W₁) : Type
    u)) :
    res f h₃₂ (res f h₂₁ s) = res f (h₃₂.trans h₂₁) s := by
  change (f.kaehler.val.presheaf.map (homOfLE h₂₁).op ≫ f.kaehler.val.presheaf.map (homOfLE
      h₃₂).op) s = _
  rw [← Functor.map_comp]
  rfl

lemma res_toSh {W' W : X.Opens} (i : W' ≤ W) (w : (f.kaehlerPresheaf.obj (op W) : Type u)) :
    res f i (f.kaehlerToSections W w) = f.kaehlerToSections W' (pmap f i w) := by
  have hnat := (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    f.kaehlerPresheaf)).naturality (homOfLE i).op
  exact (congrArg (fun φ => φ.hom w) hnat).symm

lemma toSh_locally_injective {W : X.Opens} (w w' : (f.kaehlerPresheaf.obj (op W) : Type u))
    (h : f.kaehlerToSections W w = f.kaehlerToSections W w') (x : X) (hx : x ∈ W) :
    ∃ (V : X.Opens) (i : V ≤ W), x ∈ V ∧ pmap f i w = pmap f i w' := by
  have hli : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) f.kaehlerPresheaf.presheaf) :=
          inferInstance
  have hmem := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) f.kaehlerPresheaf.presheaf) (X := op
        W)
    (show f.kaehlerPresheaf.presheaf.obj (op W) from w) (show f.kaehlerPresheaf.presheaf.obj (op W)
        from w') h
  obtain ⟨V, g, hg, hxV⟩ := hmem x hx
  refine ⟨V, g.le, hxV, ?_⟩
  change (f.kaehlerPresheaf.map (homOfLE g.le).op).hom w = (f.kaehlerPresheaf.map (homOfLE
      g.le).op).hom w'
  rw [show homOfLE g.le = g from Subsingleton.elim _ _]
  exact hg

lemma toSh_locally_surjective {W : X.Opens} (c : (Γ(f.kaehler, W) : Type u)) (x : X) (hx : x ∈ W) :
    ∃ (V : X.Opens) (i : V ≤ W), x ∈ V ∧ ∃ w : (f.kaehlerPresheaf.obj (op V) : Type u),
      f.kaehlerToSections V w = res f i c := by
  have hls : TopCat.Presheaf.IsLocallySurjective
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) f.kaehlerPresheaf.presheaf) :=
    (inferInstance : CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) f.kaehlerPresheaf.presheaf))
  obtain ⟨V, i, ⟨w, hw⟩, hxV⟩ := (TopCat.Presheaf.isLocallySurjective_iff _).mp hls W c x hx
  exact ⟨V, i, hxV, show (f.kaehlerPresheaf.obj (op V) : Type u) from w, hw⟩

lemma sections_eq_of_locally_eq {W : X.Opens} (c c' : (Γ(f.kaehler, W) : Type u))
    (h : ∀ x ∈ W, ∃ (V : X.Opens) (i : V ≤ W), x ∈ V ∧ res f i c = res f i c') : c = c' := by
  choose V i hxV hV using h
  let D : TopCat.Sheaf Ab X.toTopCat := ⟨f.kaehler.val.presheaf, f.kaehler.isSheaf⟩
  exact D.eq_of_locally_eq' (fun p : {x // x ∈ W} => V p.1 p.2) W (fun p => homOfLE (i p.1 p.2))
    (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV x hx⟩) c c' (fun p => hV p.1 p.2)

end KaehlerSections

namespace KaehlerSections

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

lemma le_left {W : X.Opens} (a b : Γ(X, W)) : X.basicOpen (a * b) ≤ X.basicOpen a :=
  (X.basicOpen_mul a b).le.trans inf_le_left

lemma le_right {W : X.Opens} (a b : Γ(X, W)) : X.basicOpen (a * b) ≤ X.basicOpen b :=
  (X.basicOpen_mul a b).le.trans inf_le_right

theorem glue {W : X.Opens} (hW : IsAffineOpen W) {ι : Type u} [Finite ι] (t : ι → Γ(X, W))
    (ht : Ideal.span (Set.range t) = ⊤)
    (m : ∀ i, (f.kaehlerPresheaf.obj (op (X.basicOpen (t i))) : Type u))
    (hm : ∀ i j, pmap f (le_left (t i) (t j)) (m i) = pmap f (le_right (t i) (t j)) (m j)) :
    ∃! w : (f.kaehlerPresheaf.obj (op W) : Type u), ∀ i, pmap f (X.basicOpen_le (t i)) w = m i := by
  classical
  let algW : Algebra A Γ(X, W) := f.sectionsAlgebra W
  let algD : ∀ g : Γ(X, W), Algebra A Γ(X, X.basicOpen g) := fun g => f.sectionsAlgebra
      (X.basicOpen g)
  have tower : ∀ g : Γ(X, W), IsScalarTower A Γ(X, W) Γ(X, X.basicOpen g) := by
    intro g
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    have := f.constToPresheaf.naturality (homOfLE (X.basicOpen_le g)).op
    have h := congrArg (fun φ => φ.hom a) this
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, CommRingCat.hom_comp,
      RingHom.coe_comp, Function.comp_apply] at h
    exact h
  have hloc : ∀ g : Γ(X, W), IsLocalization.Away g Γ(X, X.basicOpen g) := fun g =>
      hW.isLocalization_basicOpen g
  let κ : ∀ g : Γ(X, W), Ω[Γ(X, W)⁄A] →ₗ[Γ(X, W)] Ω[Γ(X, X.basicOpen g)⁄A] :=
    fun g => KaehlerDifferential.map A A Γ(X, W) Γ(X, X.basicOpen g)
  have hκ : ∀ (g : Γ(X, W)) (w : (f.kaehlerPresheaf.obj (op W) : Type u)),
      pmap f (X.basicOpen_le g) w = κ g (show Ω[Γ(X, W)⁄A] from w) := fun g w => rfl
  have hκloc : ∀ g : Γ(X, W), IsLocalizedModule (Submonoid.powers g) (κ g) := fun g =>
    KaehlerDifferential.isLocalizedModule_map A Γ(X, W) Γ(X, X.basicOpen g) (Submonoid.powers g)
  have smul_def : ∀ (g : Γ(X, W)) (r : Γ(X, W)) (n : Ω[Γ(X, X.basicOpen g)⁄A]),
      r • n = (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom r • n := fun g r n => rfl
  have pmap_smul : ∀ {a b : Γ(X, W)} (hab : X.basicOpen b ≤ X.basicOpen a) (r : Γ(X, W))
      (n : (f.kaehlerPresheaf.obj (op (X.basicOpen a)) : Type u)),
      pmap f hab ((show Ω[Γ(X, X.basicOpen a)⁄A] → (f.kaehlerPresheaf.obj (op (X.basicOpen a)) :
          Type u) from id)
        (r • (show Ω[Γ(X, X.basicOpen a)⁄A] from n))) =
      (show Ω[Γ(X, X.basicOpen b)⁄A] → (f.kaehlerPresheaf.obj (op (X.basicOpen b)) : Type u) from
          id)
        (r • (show Ω[Γ(X, X.basicOpen b)⁄A] from pmap f hab n)) := by
    intro a b hab r n
    have hms := PresheafOfModules.map_smul f.kaehlerPresheaf (homOfLE hab).op
      ((X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom r) n
    refine hms.trans ?_
    change (X.presheaf.map (homOfLE (X.basicOpen_le a)).op ≫ X.presheaf.map (homOfLE hab).op).hom r
        •
        pmap f hab n = (X.presheaf.map (homOfLE (X.basicOpen_le b)).op).hom r • pmap f hab n
    rw [← Functor.map_comp]
    rfl
  let ρ : ∀ i j, Ω[Γ(X, X.basicOpen (t i))⁄A] →ₗ[Γ(X, W)] Ω[Γ(X, X.basicOpen (t i * t j))⁄A] := fun
      i j =>
    { toFun := fun n => show Ω[Γ(X, X.basicOpen (t i * t j))⁄A] from pmap f (le_left (t i) (t j)) n
      map_add' := fun n n' => map_add (f.kaehlerPresheaf.map (homOfLE (le_left (t i) (t
          j))).op).hom n n'
      map_smul' := fun r n => pmap_smul (le_left (t i) (t j)) r n }
  let ρ' : ∀ i j, Ω[Γ(X, X.basicOpen (t j))⁄A] →ₗ[Γ(X, W)] Ω[Γ(X, X.basicOpen (t i * t j))⁄A] :=
      fun i j =>
    { toFun := fun n => show Ω[Γ(X, X.basicOpen (t i * t j))⁄A] from pmap f (le_right (t i) (t j)) n
      map_add' := fun n n' => map_add (f.kaehlerPresheaf.map (homOfLE (le_right (t i) (t
          j))).op).hom n n'
      map_smul' := fun r n => pmap_smul (le_right (t i) (t j)) r n }
  have hρ : ∀ i j, (ρ i j).comp (κ (t i)) = κ (t i * t j) := by
    intro i j
    refine LinearMap.ext fun w => ?_
    change pmap f (le_left (t i) (t j)) (pmap f (X.basicOpen_le (t i)) w) = pmap f (X.basicOpen_le
        (t i * t j)) w
    exact pmap_pmap f _ _ w
  have hρ' : ∀ i j, (ρ' i j).comp (κ (t j)) = κ (t i * t j) := by
    intro i j
    refine LinearMap.ext fun w => ?_
    change pmap f (le_right (t i) (t j)) (pmap f (X.basicOpen_le (t j)) w) = pmap f (X.basicOpen_le
        (t i * t j)) w
    exact pmap_pmap f _ _ w
  have key := IsLocalizedModule.existsUnique_forall_eq_of_span_range_eq_top t ht
    (fun i => κ (t i)) (fun i j => κ (t i * t j)) ρ ρ' hρ hρ'
    (fun i => show Ω[Γ(X, X.basicOpen (t i))⁄A] from m i) (fun i j => hm i j)
  exact key

end KaehlerSections

namespace KaehlerSections

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

lemma exists_finite_family {W : X.Opens} (hW : IsAffineOpen W) (Q : Γ(X, W) → Prop)
    (h : ∀ x ∈ W, ∃ g : Γ(X, W), x ∈ X.basicOpen g ∧ Q g) :
    ∃ (T : Finset Γ(X, W)), Ideal.span (Set.range fun s : ↥T => (s : Γ(X, W))) = ⊤ ∧ ∀ s : ↥T, Q s
        := by
  classical
  choose g hxg hQ using h
  have hspan : Ideal.span (Set.range fun p : {x // x ∈ W} => g p.1 p.2) = ⊤ := by
    rw [← hW.iSup_basicOpen_eq_self_iff]
    refine le_antisymm (iSup_le fun s => X.basicOpen_le _) fun x hx => ?_
    exact Opens.mem_iSup.mpr ⟨⟨g x hx, ⟨x, hx⟩, rfl⟩, hxg x hx⟩
  obtain ⟨T, hTsub, hT1⟩ := Submodule.mem_span_finite_of_mem_span
    ((Ideal.eq_top_iff_one _).mp hspan)
  refine ⟨T, ?_, fun s => ?_⟩
  · rw [Ideal.eq_top_iff_one]
    have : Set.range (fun s : ↥T => (s : Γ(X, W))) = (T : Set Γ(X, W)) := by
      exact Subtype.range_coe
    rw [this]; exact hT1
  · obtain ⟨⟨x, hx⟩, hgx⟩ := hTsub s.2
    rw [← hgx]; exact hQ x hx

theorem toSh_injective {W : X.Opens} (hW : IsAffineOpen W) : Function.Injective
    (f.kaehlerToSections W) := by
  classical
  intro w w' h
  have key : ∀ x ∈ W, ∃ g : Γ(X, W), x ∈ X.basicOpen g ∧
      pmap f (X.basicOpen_le g) w = pmap f (X.basicOpen_le g) w' := by
    intro x hx
    obtain ⟨V, i, hxV, hV⟩ := toSh_locally_injective f w w' h x hx
    obtain ⟨g, hgV, hxg⟩ := hW.exists_basicOpen_le ⟨x, hxV⟩ hx
    refine ⟨g, hxg, ?_⟩
    rw [← pmap_pmap f i hgV w, ← pmap_pmap f i hgV w', hV]
  obtain ⟨T, hT, hTQ⟩ := exists_finite_family hW _ key
  obtain ⟨w₀, -, huniq⟩ := glue f hW (fun s : ↥T => (s : Γ(X, W))) hT
    (fun s => pmap f (X.basicOpen_le _) w) (fun i j => by rw [pmap_pmap, pmap_pmap])
  have e1 : w = w₀ := huniq w (fun i => rfl)
  have e2 : w' = w₀ := huniq w' (fun i => (hTQ i).symm)
  rw [e1, e2]

theorem toSh_surjective {U : X.Opens} (hU : IsAffineOpen U) : Function.Surjective
    (f.kaehlerToSections U) := by
  classical
  intro c
  have key : ∀ x ∈ U, ∃ g : Γ(X, U), x ∈ X.basicOpen g ∧
      ∃ w : (f.kaehlerPresheaf.obj (op (X.basicOpen g)) : Type u),
        f.kaehlerToSections (X.basicOpen g) w = res f (X.basicOpen_le g) c := by
    intro x hx
    obtain ⟨V, i, hxV, w, hw⟩ := toSh_locally_surjective f c x hx
    obtain ⟨g, hgV, hxg⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ hx
    refine ⟨g, hxg, pmap f hgV w, ?_⟩
    rw [← res_toSh, hw, res_res]
  obtain ⟨T, hT, hTQ⟩ := exists_finite_family hU _ key
  choose m hm using hTQ
  have hcompat : ∀ i j : ↥T, pmap f (le_left (i : Γ(X, U)) j) (m i) = pmap f (le_right (i : Γ(X,
      U)) j) (m j) := by
    intro i j
    apply toSh_injective f (hU.basicOpen ((i : Γ(X, U)) * j))
    rw [← res_toSh, ← res_toSh, hm i, hm j, res_res, res_res]
  obtain ⟨w₀, hw₀, -⟩ := glue f hU (fun s : ↥T => (s : Γ(X, U))) hT m hcompat
  refine ⟨w₀, ?_⟩
  have hcov : ∀ x ∈ U, ∃ s : ↥T, x ∈ X.basicOpen (s : Γ(X, U)) := by
    intro x hx
    have hsup : ⨆ s : ↥(Set.range fun s : ↥T => (s : Γ(X, U))), X.basicOpen (s : Γ(X, U)) = U :=
      hU.iSup_basicOpen_eq_self_iff.mpr hT
    have hx' : x ∈ (⨆ s : ↥(Set.range fun s : ↥T => (s : Γ(X, U))), X.basicOpen (s : Γ(X, U))) := by
      rw [hsup]; exact hx
    obtain ⟨⟨_, ⟨s, rfl⟩⟩, hs⟩ := Opens.mem_iSup.mp hx'
    exact ⟨s, hs⟩
  apply sections_eq_of_locally_eq f
  intro x hx
  obtain ⟨s, hs⟩ := hcov x hx
  refine ⟨X.basicOpen (s : Γ(X, U)), X.basicOpen_le _, hs, ?_⟩
  rw [res_toSh, hw₀ s, hm s]

end KaehlerSections

theorem _root_.AlgebraicGeometry.Scheme.Hom.kaehlerToSections_bijective_of_isAffineOpen
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Bijective (f.kaehlerToSections U) := by
  exact ⟨KaehlerSections.toSh_injective f hU, KaehlerSections.toSh_surjective f hU⟩

end AffineDifferentialSections
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_topToSections_bijective_of_isAffineOpen.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace AffineExteriorSections
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace ExteriorSections
open AbelianVarieties.NOSProofs.AffineDifferentialSections.KaehlerSections
  (pmap pmap_pmap res_toSh exists_finite_family le_left le_right)

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ)

/-- The exterior power presheaf of the sheafified differential module. -/
noncomputable abbrev pre : X.PresheafOfModules :=
  (Scheme.Modules.presheafExteriorPower X d).obj f.kaehler.val

/-- The sheafification unit for the exterior power presheaf. -/
noncomputable def unitD (W : X.Opens) : (⋀[Γ(X, W)]^d Γ(f.kaehler, W)) → Γ(f.topDifferentials d, W)
    :=
  fun w => ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (pre f
      d)).app
    (op W) (show (pre f d).obj (op W) from w)

lemma topToSections_eq (W : X.Opens) (s : ⋀[Γ(X, W)]^d (f.kaehlerPresheaf.obj (op W))) :
    f.topToSections d W s = unitD f d W (exteriorPower.map d (f.kaehlerToSectionsₗ W) s) := rfl

lemma unitD_add (W : X.Opens) (w w' : ⋀[Γ(X, W)]^d Γ(f.kaehler, W)) :
    unitD f d W (w + w') = unitD f d W w + unitD f d W w' :=
  map_add (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (pre f
      d)).app
    (op W)).hom _ _

lemma unitD_smul (W : X.Opens) (r : Γ(X, W)) (w : ⋀[Γ(X, W)]^d Γ(f.kaehler, W)) :
    unitD f d W (r • w) = r • unitD f d W w :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (pre f d)).app
    (op W)).hom.map_smul r _

/-- Restriction of sections of the exterior power sheaf. -/
noncomputable abbrev resD {W' W : X.Opens} (h : W' ≤ W) (s : Γ(f.topDifferentials d, W)) :
    Γ(f.topDifferentials d, W') :=
  (f.topDifferentials d).presheaf.map (homOfLE h).op s

lemma resD_resD {W₁ W₂ W₃ : X.Opens} (h₂₁ : W₂ ≤ W₁) (h₃₂ : W₃ ≤ W₂) (s : Γ(f.topDifferentials d,
    W₁)) :
    resD f d h₃₂ (resD f d h₂₁ s) = resD f d (h₃₂.trans h₂₁) s := by
  change ((f.topDifferentials d).presheaf.map (homOfLE h₂₁).op ≫
    (f.topDifferentials d).presheaf.map (homOfLE h₃₂).op) s = _
  rw [← Functor.map_comp]
  rfl

lemma resD_smul {W' W : X.Opens} (h : W' ≤ W) (r : Γ(X, W)) (s : Γ(f.topDifferentials d, W)) :
    resD f d h (r • s) = X.presheaf.map (homOfLE h).op r • resD f d h s :=
  Scheme.Modules.map_smul _ (homOfLE h) r s

/-- Restriction in the exterior power presheaf. -/
noncomputable abbrev preMap {W W' : X.Opens} (h : W' ≤ W) (w : ⋀[Γ(X, W)]^d Γ(f.kaehler, W)) :
    ⋀[Γ(X, W')]^d Γ(f.kaehler, W') :=
  show ⋀[Γ(X, W')]^d Γ(f.kaehler, W') from (pre f d).map (homOfLE h).op (show (pre f d).obj (op W)
      from w)

lemma preMap_ιMulti {W W' : X.Opens} (h : W' ≤ W) (m : Fin d → Γ(f.kaehler, W)) :
    preMap f d h (exteriorPower.ιMulti _ d m) =
      exteriorPower.ιMulti _ d (fun k => (f.kaehler.presheaf.map (homOfLE h).op : Γ(f.kaehler, W) ⟶
          _) (m k)) :=
  PresheafOfModules.exteriorPower_map_ιMulti d f.kaehler.val (homOfLE h).op m

lemma preMap_preMap {W₁ W₂ W₃ : X.Opens} (h₂₁ : W₂ ≤ W₁) (h₃₂ : W₃ ≤ W₂) (w : ⋀[Γ(X, W₁)]^d
    Γ(f.kaehler, W₁)) :
    preMap f d h₃₂ (preMap f d h₂₁ w) = preMap f d (h₃₂.trans h₂₁) w := by
  change _ = (pre f d).map ((homOfLE h₂₁).op ≫ (homOfLE h₃₂).op) (show (pre f d).obj (op W₁) from w)
  rw [PresheafOfModules.map_comp_apply]

lemma resD_unitD {W' W : X.Opens} (h : W' ≤ W) (w : ⋀[Γ(X, W)]^d Γ(f.kaehler, W)) :
    resD f d h (unitD f d W w) = unitD f d W' (preMap f d h w) := by
  have hnat := (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (pre f d))).naturality (homOfLE h).op
  exact (congrArg (fun φ => φ.hom (show (pre f d).obj (op W) from w)) hnat).symm

lemma unitD_locally_injective {W : X.Opens} (w w' : ⋀[Γ(X, W)]^d Γ(f.kaehler, W))
    (h : unitD f d W w = unitD f d W w') (x : X) (hx : x ∈ W) :
    ∃ (V : X.Opens) (i : V ≤ W), x ∈ V ∧ preMap f d i w = preMap f d i w' := by
  have hmem := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (pre f d).presheaf) (X := op W)
    (show (pre f d).presheaf.obj (op W) from w) (show (pre f d).presheaf.obj (op W) from w') h
  obtain ⟨V, g, hg, hxV⟩ := hmem x hx
  refine ⟨V, g.le, hxV, ?_⟩
  change (pre f d).map (homOfLE g.le).op (show (pre f d).obj (op W) from w) =
    (pre f d).map (homOfLE g.le).op (show (pre f d).obj (op W) from w')
  rw [show homOfLE g.le = g from Subsingleton.elim _ _]
  exact hg

lemma unitD_locally_surjective {W : X.Opens} (c : Γ(f.topDifferentials d, W)) (x : X) (hx : x ∈ W) :
    ∃ (V : X.Opens) (i : V ≤ W), x ∈ V ∧ ∃ w : ⋀[Γ(X, V)]^d Γ(f.kaehler, V), unitD f d V w = resD f
        d i c := by
  have hls : TopCat.Presheaf.IsLocallySurjective
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (pre f d).presheaf) :=
    (inferInstance : CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (pre f d).presheaf))
  obtain ⟨V, i, ⟨w, hw⟩, hxV⟩ := (TopCat.Presheaf.isLocallySurjective_iff _).mp hls W c x hx
  exact ⟨V, i, hxV, show ⋀[Γ(X, V)]^d Γ(f.kaehler, V) from w, hw⟩

lemma sections_eq_of_locally_eq {W : X.Opens} (c c' : Γ(f.topDifferentials d, W))
    (h : ∀ x ∈ W, ∃ (V : X.Opens) (i : V ≤ W), x ∈ V ∧ resD f d i c = resD f d i c') : c = c' := by
  choose V i hxV hV using h
  let D : TopCat.Sheaf Ab X.toTopCat := ⟨(f.topDifferentials d).presheaf, (f.topDifferentials
      d).isSheaf⟩
  exact D.eq_of_locally_eq' (fun p : {x // x ∈ W} => V p.1 p.2) W (fun p => homOfLE (i p.1 p.2))
    (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV x hx⟩) c c' (fun p => hV p.1 p.2)

/-- The exterior power of the Kähler differential presheaf. -/
noncomputable abbrev preK : X.PresheafOfModules := PresheafOfModules.exteriorPower d
    f.kaehlerPresheaf

/-- Restriction in the exterior power of presheaf differentials. -/
noncomputable abbrev emap {W W' : X.Opens} (h : W' ≤ W) (s : ⋀[Γ(X, W)]^d (f.kaehlerPresheaf.obj
    (op W))) :
    ⋀[Γ(X, W')]^d (f.kaehlerPresheaf.obj (op W')) :=
  show ⋀[Γ(X, W')]^d (f.kaehlerPresheaf.obj (op W')) from
    (preK f d).map (homOfLE h).op (show (preK f d).obj (op W) from s)

lemma emap_ιMulti {W W' : X.Opens} (h : W' ≤ W) (m : Fin d → (f.kaehlerPresheaf.obj (op W) : Type
    u)) :
    emap f d h (exteriorPower.ιMulti _ d m) = exteriorPower.ιMulti _ d (fun k => pmap f h (m k)) :=
  PresheafOfModules.exteriorPower_map_ιMulti d f.kaehlerPresheaf (homOfLE h).op m

lemma emap_emap {W₁ W₂ W₃ : X.Opens} (h₂₁ : W₂ ≤ W₁) (h₃₂ : W₃ ≤ W₂)
    (s : ⋀[Γ(X, W₁)]^d (f.kaehlerPresheaf.obj (op W₁))) :
    emap f d h₃₂ (emap f d h₂₁ s) = emap f d (h₃₂.trans h₂₁) s := by
  change _ = (preK f d).map ((homOfLE h₂₁).op ≫ (homOfLE h₃₂).op) (show (preK f d).obj (op W₁) from
      s)
  rw [PresheafOfModules.map_comp_apply]

lemma emap_add {W W' : X.Opens} (h : W' ≤ W) (s s' : ⋀[Γ(X, W)]^d (f.kaehlerPresheaf.obj (op W))) :
    emap f d h (s + s') = emap f d h s + emap f d h s' :=
  map_add ((preK f d).map (homOfLE h).op).hom _ _

lemma emap_smul {W W' : X.Opens} (h : W' ≤ W) (r : Γ(X, W)) (s : ⋀[Γ(X, W)]^d
    (f.kaehlerPresheaf.obj (op W))) :
    emap f d h (r • s) = X.presheaf.map (homOfLE h).op r • emap f d h s :=
  (preK f d).map_smul (homOfLE h).op r (show (preK f d).obj (op W) from s)

/-- The exterior power of the differential sheafification map. -/
noncomputable abbrev Λ (W : X.Opens) :
    ⋀[Γ(X, W)]^d (f.kaehlerPresheaf.obj (op W)) →ₗ[Γ(X, W)] ⋀[Γ(X, W)]^d Γ(f.kaehler, W) :=
  exteriorPower.map d (f.kaehlerToSectionsₗ W)

lemma preMap_Λ {W W' : X.Opens} (h : W' ≤ W) (s : ⋀[Γ(X, W)]^d (f.kaehlerPresheaf.obj (op W))) :
    preMap f d h (Λ f d W s) = Λ f d W' (emap f d h s) := by
  let η : f.kaehlerPresheaf ⟶ f.kaehler.val :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      f.kaehlerPresheaf
  let ηd : preK f d ⟶ pre f d :=
    PresheafOfModules.exteriorPowerMap (R := X.sheaf.obj) d η
  exact (PresheafOfModules.naturality_apply ηd (homOfLE h).op s).symm

lemma resD_top {W W' : X.Opens} (h : W' ≤ W) (s : ⋀[Γ(X, W)]^d (f.kaehlerPresheaf.obj (op W))) :
    resD f d h (f.topToSections d W s) = f.topToSections d W' (emap f d h s) := by
  rw [topToSections_eq, topToSections_eq, resD_unitD, preMap_Λ]

lemma Λ_bijective {W : X.Opens} (hW : IsAffineOpen W) : Function.Bijective (Λ f d W) := by
  have hb : Function.Bijective (f.kaehlerToSectionsₗ W) :=
    AlgebraicGeometry.Scheme.Hom.kaehlerToSections_bijective_of_isAffineOpen f hW
  let e := LinearEquiv.ofBijective (f.kaehlerToSectionsₗ W) hb
  let E : ⋀[Γ(X, W)]^d (f.kaehlerPresheaf.obj (op W)) ≃ₗ[Γ(X, W)] ⋀[Γ(X, W)]^d Γ(f.kaehler, W) :=
    LinearEquiv.ofLinearMap (exteriorPower.map d e.toLinearMap) (exteriorPower.map d
        e.symm.toLinearMap)
      (by rw [← exteriorPower.map_comp, LinearEquiv.comp_symm, exteriorPower.map_id])
      (by rw [← exteriorPower.map_comp, LinearEquiv.symm_comp, exteriorPower.map_id])
  have : (E : ⋀[Γ(X, W)]^d (f.kaehlerPresheaf.obj (op W)) →ₗ[Γ(X, W)] ⋀[Γ(X, W)]^d Γ(f.kaehler, W))
      = Λ f d W := rfl
  rw [← this]
  exact E.bijective

end ExteriorSections

namespace ExteriorSections
open AbelianVarieties.NOSProofs.AffineDifferentialSections.KaehlerSections
  (pmap pmap_pmap res_toSh exists_finite_family le_left le_right)

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ)

theorem glue {W : X.Opens} (hW : IsAffineOpen W) {ι : Type u} [Finite ι] (t : ι → Γ(X, W))
    (ht : Ideal.span (Set.range t) = ⊤)
    (m : ∀ i, ⋀[Γ(X, X.basicOpen (t i))]^d (f.kaehlerPresheaf.obj (op (X.basicOpen (t i)))))
    (hm : ∀ i j, emap f d (le_left (t i) (t j)) (m i) = emap f d (le_right (t i) (t j)) (m j)) :
    ∃! s : ⋀[Γ(X, W)]^d (f.kaehlerPresheaf.obj (op W)), ∀ i, emap f d (X.basicOpen_le (t i)) s = m
        i := by
  classical
  let algW : Algebra A Γ(X, W) := f.sectionsAlgebra W
  let algD : ∀ g : Γ(X, W), Algebra A Γ(X, X.basicOpen g) := fun g => f.sectionsAlgebra
      (X.basicOpen g)
  have tower : ∀ g : Γ(X, W), IsScalarTower A Γ(X, W) Γ(X, X.basicOpen g) := by
    intro g
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    have := f.constToPresheaf.naturality (homOfLE (X.basicOpen_le g)).op
    have h := congrArg (fun φ => φ.hom a) this
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
      CommRingCat.hom_comp] at h
    exact h
  have hloc : ∀ g : Γ(X, W), IsLocalization.Away g Γ(X, X.basicOpen g) := fun g =>
      hW.isLocalization_basicOpen g
  let κ : ∀ g : Γ(X, W), Ω[Γ(X, W)⁄A] →ₗ[Γ(X, W)] Ω[Γ(X, X.basicOpen g)⁄A] :=
    fun g => KaehlerDifferential.map A A Γ(X, W) Γ(X, X.basicOpen g)
  have hκ : ∀ (g : Γ(X, W)) (w : (f.kaehlerPresheaf.obj (op W) : Type u)),
      pmap f (X.basicOpen_le g) w = κ g (show Ω[Γ(X, W)⁄A] from w) := fun g w => rfl
  have hκloc : ∀ g : Γ(X, W), IsLocalizedModule (Submonoid.powers g) (κ g) := fun g =>
    KaehlerDifferential.isLocalizedModule_map A Γ(X, W) Γ(X, X.basicOpen g) (Submonoid.powers g)
  have towerΩ : ∀ g : Γ(X, W), IsScalarTower Γ(X, W) Γ(X, X.basicOpen g) (Ω[Γ(X, X.basicOpen g)⁄A])
      :=
    fun g => KaehlerDifferential.isScalarTower_of_tower A Γ(X, X.basicOpen g)
  let modN : ∀ g : Γ(X, W), Module Γ(X, W) (f.kaehlerPresheaf.obj (op (X.basicOpen g))) :=
    fun g => (inferInstance : Module Γ(X, W) (Ω[Γ(X, X.basicOpen g)⁄A]))
  have towerN : ∀ g : Γ(X, W),
      IsScalarTower Γ(X, W) Γ(X, X.basicOpen g) (f.kaehlerPresheaf.obj (op (X.basicOpen g))) :=
    fun g => towerΩ g
  have emap_smulW : ∀ {a b : Γ(X, W)} (hab : X.basicOpen b ≤ X.basicOpen a) (r : Γ(X, W))
      (s : ⋀[Γ(X, X.basicOpen a)]^d (f.kaehlerPresheaf.obj (op (X.basicOpen a)))),
      emap f d hab (r • s) = r • emap f d hab s := by
    intro a b hab r s
    rw [← algebraMap_smul Γ(X, X.basicOpen a) r s, emap_smul,
      ← algebraMap_smul Γ(X, X.basicOpen b) r (emap f d hab s)]
    congr 1
    change (X.presheaf.map (homOfLE (X.basicOpen_le a)).op ≫ X.presheaf.map (homOfLE hab).op).hom r
        = _
    rw [← Functor.map_comp]
    rfl
  let E : ∀ g : Γ(X, W), ⋀[Γ(X, W)]^d (f.kaehlerPresheaf.obj (op W)) →ₗ[Γ(X, W)]
      ⋀[Γ(X, X.basicOpen g)]^d (f.kaehlerPresheaf.obj (op (X.basicOpen g))) := fun g =>
    { toFun := fun s => emap f d (X.basicOpen_le g) s
      map_add' := fun s s' => emap_add f d _ s s'
      map_smul' := fun r s => by
        rw [RingHom.id_apply, ← algebraMap_smul Γ(X, X.basicOpen g) r (emap f d _ s)]
        exact emap_smul f d _ r s }
  have hEloc : ∀ g : Γ(X, W), IsLocalizedModule (Submonoid.powers g) (E g) := fun g => by
    exact @IsLocalizedModule.of_forall_apply_iotaMulti_eq _ _ (Submonoid.powers g) Γ(X, X.basicOpen
        g)
      _ _ _ _ _ _ _ _ _ _ (towerΩ g) (κ g) (hκloc g) d (E g)
      (fun mm => emap_ιMulti f d (X.basicOpen_le g) mm)
  let ρ : ∀ i j, ⋀[Γ(X, X.basicOpen (t i))]^d (f.kaehlerPresheaf.obj (op (X.basicOpen (t i))))
      →ₗ[Γ(X, W)]
      ⋀[Γ(X, X.basicOpen (t i * t j))]^d (f.kaehlerPresheaf.obj (op (X.basicOpen (t i * t j)))) :=
          fun i j =>
    { toFun := fun s => emap f d (le_left (t i) (t j)) s
      map_add' := fun s s' => emap_add f d _ s s'
      map_smul' := fun r s => emap_smulW (le_left (t i) (t j)) r s }
  let ρ' : ∀ i j, ⋀[Γ(X, X.basicOpen (t j))]^d (f.kaehlerPresheaf.obj (op (X.basicOpen (t j))))
      →ₗ[Γ(X, W)]
      ⋀[Γ(X, X.basicOpen (t i * t j))]^d (f.kaehlerPresheaf.obj (op (X.basicOpen (t i * t j)))) :=
          fun i j =>
    { toFun := fun s => emap f d (le_right (t i) (t j)) s
      map_add' := fun s s' => emap_add f d _ s s'
      map_smul' := fun r s => emap_smulW (le_right (t i) (t j)) r s }
  have hρ : ∀ i j, (ρ i j).comp (E (t i)) = E (t i * t j) := by
    intro i j
    refine LinearMap.ext fun s => ?_
    change emap f d (le_left (t i) (t j)) (emap f d (X.basicOpen_le (t i)) s) = emap f d
        (X.basicOpen_le (t i * t j)) s
    rw [emap_emap]
  have hρ' : ∀ i j, (ρ' i j).comp (E (t j)) = E (t i * t j) := by
    intro i j
    refine LinearMap.ext fun s => ?_
    change emap f d (le_right (t i) (t j)) (emap f d (X.basicOpen_le (t j)) s) = emap f d
        (X.basicOpen_le (t i * t j)) s
    rw [emap_emap]
  exact IsLocalizedModule.existsUnique_forall_eq_of_span_range_eq_top t ht
    (fun i => E (t i)) (fun i j => E (t i * t j)) ρ ρ' hρ hρ' m (fun i j => hm i j)

theorem top_injective {W : X.Opens} (hW : IsAffineOpen W) : Function.Injective (f.topToSections d
    W) := by
  classical
  intro s s' h
  have key : ∀ x ∈ W, ∃ g : Γ(X, W), x ∈ X.basicOpen g ∧
      emap f d (X.basicOpen_le g) s = emap f d (X.basicOpen_le g) s' := by
    intro x hx
    rw [topToSections_eq, topToSections_eq] at h
    obtain ⟨V, i, hxV, hV⟩ := unitD_locally_injective f d _ _ h x hx
    obtain ⟨g, hgV, hxg⟩ := hW.exists_basicOpen_le ⟨x, hxV⟩ hx
    refine ⟨g, hxg, (Λ_bijective f d (hW.basicOpen g)).1 ?_⟩
    have e1 : ∀ s₁ : ⋀[Γ(X, W)]^d (f.kaehlerPresheaf.obj (op W)),
        Λ f d (X.basicOpen g) (emap f d (X.basicOpen_le g) s₁) = preMap f d hgV (preMap f d i (Λ f
            d W s₁)) := by
      intro s₁; rw [preMap_preMap, preMap_Λ]
    rw [e1, e1, hV]
  obtain ⟨T, hT, hTQ⟩ := exists_finite_family hW _ key
  obtain ⟨s₀, -, huniq⟩ := glue f d hW (fun u : ↥T => (u : Γ(X, W))) hT
    (fun u => emap f d (X.basicOpen_le _) s) (fun i j => by rw [emap_emap, emap_emap])
  have e1 : s = s₀ := huniq s (fun i => rfl)
  have e2 : s' = s₀ := huniq s' (fun i => (hTQ i).symm)
  rw [e1, e2]

theorem top_surjective {U : X.Opens} (hU : IsAffineOpen U) : Function.Surjective (f.topToSections d
    U) := by
  classical
  intro c
  have key : ∀ x ∈ U, ∃ g : Γ(X, U), x ∈ X.basicOpen g ∧
      ∃ s : ⋀[Γ(X, X.basicOpen g)]^d (f.kaehlerPresheaf.obj (op (X.basicOpen g))),
        f.topToSections d (X.basicOpen g) s = resD f d (X.basicOpen_le g) c := by
    intro x hx
    obtain ⟨V, i, hxV, w, hw⟩ := unitD_locally_surjective f d c x hx
    obtain ⟨g, hgV, hxg⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ hx
    obtain ⟨s, hs⟩ := (Λ_bijective f d (hU.basicOpen g)).2 (preMap f d hgV w)
    refine ⟨g, hxg, s, ?_⟩
    rw [topToSections_eq, hs, ← resD_unitD, hw, resD_resD]
  obtain ⟨T, hT, hTQ⟩ := exists_finite_family hU _ key
  choose m hm using hTQ
  have hcompat : ∀ i j : ↥T, emap f d (le_left (i : Γ(X, U)) j) (m i) = emap f d (le_right (i :
      Γ(X, U)) j) (m j) := by
    intro i j
    apply top_injective f d (hU.basicOpen ((i : Γ(X, U)) * j))
    rw [← resD_top, ← resD_top, hm i, hm j, resD_resD, resD_resD]
  obtain ⟨s₀, hs₀, -⟩ := glue f d hU (fun u : ↥T => (u : Γ(X, U))) hT m hcompat
  refine ⟨s₀, ?_⟩
  have hcov : ∀ x ∈ U, ∃ u : ↥T, x ∈ X.basicOpen (u : Γ(X, U)) := by
    intro x hx
    have hsup : ⨆ u : ↥(Set.range fun u : ↥T => (u : Γ(X, U))), X.basicOpen (u : Γ(X, U)) = U :=
      hU.iSup_basicOpen_eq_self_iff.mpr hT
    have hx' : x ∈ (⨆ u : ↥(Set.range fun u : ↥T => (u : Γ(X, U))), X.basicOpen (u : Γ(X, U))) := by
      rw [hsup]; exact hx
    obtain ⟨⟨_, ⟨u, rfl⟩⟩, hu⟩ := Opens.mem_iSup.mp hx'
    exact ⟨u, hu⟩
  apply sections_eq_of_locally_eq f d
  intro x hx
  obtain ⟨u, hu⟩ := hcov x hx
  refine ⟨X.basicOpen (u : Γ(X, U)), X.basicOpen_le _, hu, ?_⟩
  rw [resD_top, hs₀ u, hm u]

end ExteriorSections

theorem _root_.AlgebraicGeometry.Scheme.Hom.topToSections_bijective_of_isAffineOpen
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (d : ℕ) {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Bijective (f.topToSections d U) := by
  exact ⟨ExteriorSections.top_injective f d hU, ExteriorSections.top_surjective f d hU⟩

end AffineExteriorSections
end NOSProofs
end AbelianVarieties
end
