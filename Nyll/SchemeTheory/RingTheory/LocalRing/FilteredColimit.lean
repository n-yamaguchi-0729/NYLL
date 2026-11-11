/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Local rings and residue fields of actual filtered colimits

All constructions use the supplied commutative-ring cocone and its
original maps. Units lift to a later stage, so local transition maps
make the original cocone maps local. The actual colimit of local rings
is local, and its native residue field is the colimit of the native
stage residue fields.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace CommRingCat

variable {I : Type u} [SmallCategory I] [IsFiltered I]

/-- A unit in the actual filtered colimit is already a unit after an
actual transition from its specified stage. -/
theorem isUnit_ι_iff_of_isColimit (D : I ⥤ CommRingCat.{u})
    (c : Cocone D) (hc : IsColimit c) (i : I) (x : D.obj i) :
    IsUnit (c.ι.app i x) ↔ ∃ (j : I) (f : i ⟶ j), IsUnit (D.map f x) := by
  constructor
  · intro hx
    obtain ⟨y, hxy⟩ := hx.exists_right_inv
    have hrep : ∃ (j : I) (z : D.obj j), c.ι.app j z = y := by
      exact Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves (forget CommRingCat.{u}) hc) y
    obtain ⟨j, z, hz⟩ := hrep
    let k := IsFiltered.max i j
    let p : i ⟶ k := IsFiltered.leftToMax i j
    let q : j ⟶ k := IsFiltered.rightToMax i j
    have hp : c.ι.app k (D.map p x) = c.ι.app i x :=
      ConcreteCategory.congr_hom (c.w p) x
    have hq : c.ι.app k (D.map q z) = y :=
      (ConcreteCategory.congr_hom (c.w q) z).trans hz
    have hmul : c.ι.app k (D.map p x * D.map q z) = c.ι.app k 1 := by
      rw [map_mul, hp, hq, map_one]
      exact hxy
    obtain ⟨l, t, ht⟩ := (Types.FilteredColimit.isColimit_eq_iff'
      (isColimitOfPreserves (forget CommRingCat.{u}) hc) _ _).mp hmul
    have hunit : IsUnit (D.map t (D.map p x)) := by
      apply isUnit_iff_exists_inv.mpr
      refine ⟨D.map t (D.map q z), ?_⟩
      change D.map t (D.map p x * D.map q z) = D.map t 1 at ht
      simpa only [map_mul, map_one] using ht
    refine ⟨l, p ≫ t, ?_⟩
    exact (ConcreteCategory.congr_hom (D.map_comp p t) x).symm ▸ hunit
  · rintro ⟨j, f, hx⟩
    have h := hx.map (c.ι.app j).hom
    exact (ConcreteCategory.congr_hom (c.w f) x) ▸ h

/-- The original maps into a filtered colimit reflect units whenever
the original transition maps do. No alternate colimit is introduced. -/
theorem isLocalHom_ι_of_isColimit (D : I ⥤ CommRingCat.{u})
    (c : Cocone D) (hc : IsColimit c)
    (hlocal : ∀ {i j : I} (f : i ⟶ j), IsLocalHom (D.map f).hom) (i : I) :
    IsLocalHom (c.ι.app i).hom := by
  constructor
  intro x hx
  obtain ⟨j, f, hf⟩ := (isUnit_ι_iff_of_isColimit D c hc i x).mp hx
  have : IsLocalHom (D.map f).hom := hlocal f
  exact isUnit_of_map_unit (D.map f).hom x hf

/-- The actual filtered colimit of local commutative rings is local.
Locality of transition maps is needed for the legs, but not for this assertion. -/
theorem isLocalRing_of_isColimit (D : I ⥤ CommRingCat.{u})
    [∀ i, IsLocalRing (D.obj i)] (c : Cocone D) (hc : IsColimit c) :
    IsLocalRing c.pt := by
  classical
  have : Nontrivial c.pt := by
    apply nontrivial_of_ne (0 : c.pt) 1
    intro h
    let i : I := Classical.choice IsFiltered.nonempty
    have he : c.ι.app i 0 = c.ι.app i 1 :=
      (map_zero (c.ι.app i).hom).trans (h.trans (map_one (c.ι.app i).hom).symm)
    obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff'
      (isColimitOfPreserves (forget CommRingCat.{u}) hc) _ _).mp he
    change D.map f 0 = D.map f 1 at hf
    exact zero_ne_one (show (0 : D.obj j) = 1 by
      simpa only [map_zero, map_one] using hf)
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro x
  have hrep : ∃ (i : I) (y : D.obj i), c.ι.app i y = x := by
    exact Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget CommRingCat.{u}) hc) x
  obtain ⟨i, y, rfl⟩ := hrep
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self y with hy | hy
  · exact Or.inl (hy.map (c.ι.app i).hom)
  · exact Or.inr (by simpa only [map_sub, map_one] using hy.map (c.ι.app i).hom)

/-- A natural diagram of local maps induces a local map on the original
colimits, with the supplied actual comparison triangles. -/
theorem isLocalHom_of_isColimits
    (A B : I ⥤ CommRingCat.{u}) (φ : A ⟶ B)
    (cA : Cocone A) (cB : Cocone B) (hA : IsColimit cA) (hB : IsColimit cB)
    (f : cA.pt ⟶ cB.pt)
    (hf : ∀ i, cA.ι.app i ≫ f = φ.app i ≫ cB.ι.app i)
    (hBlocal : ∀ {i j : I} (t : i ⟶ j), IsLocalHom (B.map t).hom)
    (hφlocal : ∀ i, IsLocalHom (φ.app i).hom) : IsLocalHom f.hom := by
  constructor
  intro x hx
  have hrep : ∃ (i : I) (y : A.obj i), cA.ι.app i y = x := by
    exact Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget CommRingCat.{u}) hA) x
  obtain ⟨i, y, rfl⟩ := hrep
  have : IsLocalHom (cB.ι.app i).hom := isLocalHom_ι_of_isColimit B cB hB hBlocal i
  have : IsLocalHom (φ.app i).hom := hφlocal i
  have hunit : IsUnit (cB.ι.app i (φ.app i y)) :=
    (ConcreteCategory.congr_hom (hf i) y) ▸ hx
  exact (isUnit_of_map_unit (φ.app i).hom y
    (isUnit_of_map_unit (cB.ι.app i).hom (φ.app i y) hunit)).map (cA.ι.app i).hom

variable (D : I ⥤ CommRingCat.{u}) [∀ i, IsLocalRing (D.obj i)]
  (hlocal : ∀ {i j : I} (f : i ⟶ j), IsLocalHom (D.map f).hom)

/-- The diagram of the actual native residue fields. -/
def localResidueDiagram : I ⥤ CommRingCat.{u} where
  obj i := CommRingCat.of (IsLocalRing.ResidueField (D.obj i))
  map f :=
    let : IsLocalHom (D.map f).hom := hlocal f
    CommRingCat.ofHom (IsLocalRing.ResidueField.map (D.map f).hom)
  map_id i := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    change IsLocalRing.residue (D.obj i) (D.map (𝟙 i) x) =
      IsLocalRing.residue (D.obj i) x
    exact congrArg (IsLocalRing.residue (D.obj i))
      (ConcreteCategory.congr_hom (D.map_id i) x)
  map_comp {i j k} f g := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    change IsLocalRing.residue (D.obj k) (D.map (f ≫ g) x) =
      IsLocalRing.residue (D.obj k) (D.map g (D.map f x))
    exact congrArg (IsLocalRing.residue (D.obj k))
      (ConcreteCategory.congr_hom (D.map_comp f g) x)

variable (c : Cocone D) (hc : IsColimit c) [IsLocalRing c.pt]

/-- The residue cocone uses the original local cocone maps. -/
def localResidueCocone : Cocone (localResidueDiagram D hlocal) where
  pt := CommRingCat.of (IsLocalRing.ResidueField c.pt)
  ι :=
    { app i :=
        let : IsLocalHom (c.ι.app i).hom := isLocalHom_ι_of_isColimit D c hc hlocal i
        CommRingCat.ofHom (IsLocalRing.ResidueField.map (c.ι.app i).hom)
      naturality i j f := by
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro x
        obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
        change IsLocalRing.residue c.pt (c.ι.app j (D.map f x)) =
          IsLocalRing.residue c.pt (c.ι.app i x)
        exact congrArg (IsLocalRing.residue c.pt) (ConcreteCategory.congr_hom (c.w f) x) }

/-- The native residue field of the actual local colimit is the colimit
of the native stage residue fields, with their original transition maps. -/
def localResidueCoconeIsColimit : IsColimit (localResidueCocone D hlocal c hc) := by
  have : ReflectsColimit (localResidueDiagram D hlocal) (forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (forget CommRingCat.{u})
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro x
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    have hrep : ∃ (i : I) (y : D.obj i), c.ι.app i y = x := by
      exact Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves (forget CommRingCat.{u}) hc) x
    obtain ⟨i, y, hy⟩ := hrep
    refine ⟨i, IsLocalRing.residue (D.obj i) y, ?_⟩
    exact congrArg (IsLocalRing.residue c.pt) hy.symm
  · intro i j x y hxy
    let k := IsFiltered.max i j
    let p : i ⟶ k := IsFiltered.leftToMax i j
    let q : j ⟶ k := IsFiltered.rightToMax i j
    refine ⟨k, p, q, ?_⟩
    let ck : CommRingCat.of (IsLocalRing.ResidueField (D.obj k)) ⟶
        CommRingCat.of (IsLocalRing.ResidueField c.pt) :=
      (localResidueCocone D hlocal c hc).ι.app k
    apply RingHom.injective ck.hom
    exact (ConcreteCategory.congr_hom
      ((localResidueCocone D hlocal c hc).w p) x).trans
      (hxy.trans (ConcreteCategory.congr_hom
        ((localResidueCocone D hlocal c hc).w q) y).symm)

end CommRingCat
