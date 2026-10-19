/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.Torus
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-! # The actual split torus commutes with extension of scalars -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.GroupSchemes

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (r : ℕ)

/-- Scalar extension of the actual character algebra preserves its Hopf operations. -/
def splitTorusAlgebraBaseChange :
    splitTorusAlgebra S r ≃ₐc[S] S ⊗[R] splitTorusAlgebra R r :=
  BialgEquiv.ofAlgEquiv (AddMonoidAlgebra.scalarTensorEquiv R S).symm
    (by
      ext m
      simp [AddMonoidAlgebra.scalarTensorEquiv_symm_single])
    (by
      ext m
      simp [AddMonoidAlgebra.scalarTensorEquiv_symm_single,
        TensorProduct.comul_tmul])

/-- The actual scheme pullback of the split torus is its split model over the new ring. -/
def splitTorusBaseChangeIso :
    (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj (splitTorus R r) ≅
      splitTorus S r := by
  let B : CommHopfAlgCat S :=
    CommHopfAlgCat.of S (S ⊗[R] splitTorusAlgebra R r)
  let G : CommGrp (Over (Spec (CommRingCat.of S))) := {
    X := ((hopfSpec (CommRingCat.of S)).obj (op B)).X
    grp := ((hopfSpec (CommRingCat.of S)).obj (op B)).grp
    comm := by
      change IsCommMonObj
        ((Spec (CommRingCat.of (S ⊗[R] splitTorusAlgebra R r))).asOver
          (Spec (CommRingCat.of S)))
      infer_instance }
  let e : ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj
      (splitTorus R r)).X ≅ G.X := by
    exact (pullbackSymmetry _ _ ≪≫
      pullbackSpecIso' R S (splitTorusAlgebra R r)).asOver (Spec (CommRingCat.of S))
  have he : IsMonHom e.hom := by
    change IsMonHom ((pullbackSymmetry _ _ ≪≫
      pullbackSpecIso' R S (splitTorusAlgebra R r)).hom.asOver (Spec (CommRingCat.of S)))
    infer_instance
  have : IsCommMonObj G.X := G.comm
  let a : (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj
      (splitTorus R r) ≅ G := CommGrp.mkIso' e
  let h : CommHopfAlgCat.of S (splitTorusAlgebra S r) ≅ B :=
    CommHopfAlgCat.isoMk (splitTorusAlgebraBaseChange R S r)
  let b : G ≅ splitTorus S r :=
    (CommGrp.fullyFaithfulForget₂Grp _).preimageIso
      ((hopfSpec (CommRingCat.of S)).mapIso h.op)
  exact a ≪≫ b

end GroupSchemes

namespace IsSplitTorus

variable {K L : Type u} [Field K] [Field L]
  {G : CommGrp (Over (Spec (CommRingCat.of K)))}

/-- A split torus remains split after every field extension. -/
instance baseChange (f : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
    [IsSplitTorus G] : IsSplitTorus ((GroupSchemes.baseChange f).obj G) := by
  let : Algebra K L := (Spec.preimage f).hom.toAlgebra
  have hf : Spec.map (CommRingCat.ofHom (algebraMap K L)) = f := Spec.map_preimage f
  obtain ⟨r, ⟨a⟩⟩ := exists_split (G := G)
  refine ⟨r, ⟨(GroupSchemes.baseChange f).mapIso a ≪≫ ?_⟩⟩
  rw [← hf]
  exact GroupSchemes.splitTorusBaseChangeIso K L r

/-- A genuine split model satisfies the geometric torus property. -/
instance isTorus [IsSplitTorus G] : IsTorus G := by
  obtain ⟨r, ⟨a⟩⟩ := exists_split (G := G)
  refine ⟨r, fun Ω _ _ f => ?_⟩
  let : Algebra K Ω := (Spec.preimage f).hom.toAlgebra
  have hf : Spec.map (CommRingCat.ofHom (algebraMap K Ω)) = f := Spec.map_preimage f
  refine ⟨(GroupSchemes.baseChange f).mapIso a ≪≫ ?_⟩
  rw [← hf]
  exact GroupSchemes.splitTorusBaseChangeIso K Ω r

end IsSplitTorus

end AlgebraicGeometry
