/- This file defines tensor bundle on a smooth manifold by the following

Let `M` be a manifold with model `I` on `(E, H),` whereas we assumed that `M` has finite dimension
The tangent space `TangentSpace I (x : M)` has already been defined as a type synonym for `E`,
and the tangent bundle `TangentBundle I M` as an abbrev of `Bundle.TotalSpace E (TangentSpace I : M → Type _)`.

We define `Tensor0SSpace (s : ℕ)` by s-multilinear map from `TangentSpace` to the base field,
which in finite dimension is isomorphic to the (0,s) tensors (covariant tensors).
Consideration for Banach manifold is left for a future project.
`Tensor0SBundle` is the abbreviation Bundle.TotalSpace (Tensor0SModel 𝕜 E s) (Tensor0SSpace s I : M → Type _)

After some clearance of inference problem, we inductively construct a structure `tensor0SBundleData (s: ℕ)`
which stores four instances `topology` `fiber` `vector` `smooth,` that the (0,s) tensor bundle is
a topological space, a fibre bundle, a vector bundle, and a smooth vector bundle respectively.

We finally define (r,s) tensor bundle as the hom bundle from (0,r) tensor bundle to (0,s) tensor bundle,
then show the instance `tensorRSBundle_smooth (r s : ℕ)`
  ContMDiffVectorBundle n
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜 →L[𝕜]
     ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
      (fun x : M => Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x) I

To do:
verify actually (0,1) bundle is cotangent bundle
Einstein convention/ Frame Bundle?
Lie Derivative
-/


import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.LinearMap

namespace Tensor0SBundle
noncomputable section

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I ω M]
variable {x' : M}
variable {r s : ℕ}

abbrev TrivialBundle : M → Type _ := fun _ ↦  𝕜

-- Tensor0SSpace is multilinear maps from tangent spaces to the base field
-- These are (0,s) covariant tensors
@[reducible]
def Tensor0SSpace (s : ℕ) (I : ModelWithCorners 𝕜 E H) (x : M) :=
  ContinuousMultilinearMap 𝕜 (fun _ : Fin s => TangentSpace I x) 𝕜

instance (x : M) : Inhabited (Tensor0SSpace s I x) := by infer_instance

noncomputable instance (s : ℕ) :
    NormedAddCommGroup (E →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) :=
  @ContinuousLinearMap.toNormedAddCommGroup 𝕜 𝕜
    E (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
    _ _ _ _ _ _
    (RingHom.id 𝕜)
    _

noncomputable def tensor0S_curry
    (s : ℕ) (x : M) :
  Tensor0SSpace (s+1) I x ≃L[𝕜] (TangentSpace I x →L[𝕜] Tensor0SSpace s I x) := by
  unfold TangentSpace
  exact (continuousMultilinearCurryLeftEquiv 𝕜
    (fun _ : Fin (s+1) => E) 𝕜).toContinuousLinearEquiv

-- Fiberwise instances for (0,s)-tensors
noncomputable instance tensor0SSpace_normedAddCommGroup (s : ℕ) (x : M) :
    NormedAddCommGroup (Tensor0SSpace s I x) := by
  unfold Tensor0SSpace
  unfold TangentSpace
  infer_instance

noncomputable instance tensor0SSpace_normedSpace (s : ℕ) (x : M) :
    NormedSpace 𝕜 (Tensor0SSpace s I x) := by
  unfold Tensor0SSpace
  unfold TangentSpace
  infer_instance

-- Fiberwise instances for (r,s)-tensors as Hom((0,r), (0,s))
noncomputable instance tensorRSSpace_normedSpace (r s : ℕ) (x : M) :
    NormedSpace 𝕜 (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x) :=
  inferInstance

noncomputable instance tensorRSSpace_continuousSMul (r s : ℕ) (x : M) :
    ContinuousSMul 𝕜 (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x) :=
  inferInstance

noncomputable instance tensorRSModel_topology (r s : ℕ) :
    TopologicalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) :=
  letI : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜) := inferInstance
  letI : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) := inferInstance
  inferInstance

noncomputable instance tensor0SModel_normedAddCommGroup (s : ℕ) :
    NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) :=
  inferInstance

noncomputable instance tensor0SModel_normedSpace (s : ℕ) :
    NormedSpace 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) :=
  inferInstance

-- Model fiber instances for (r,s)-tensors
noncomputable instance tensorRSModel_normedAddCommGroup (r s : ℕ) :
    NormedAddCommGroup
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) :=
  inferInstance

noncomputable instance tensorRSModel_normedSpace (r s : ℕ) :
    NormedSpace 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) :=
  inferInstance

-- Topology instances for (0,0)-tensor bundle
noncomputable instance tensor0S_topologicalSpace_zero :
    TopologicalSpace (TotalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E) 𝕜)
      (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => TangentSpace I x) 𝕜)) := by
  have h : (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => TangentSpace I x) 𝕜) =
           (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E) 𝕜) := by
    ext x
    unfold TangentSpace
    rfl
  rw [h]
  infer_instance

noncomputable instance tensor0S_fiberBundle_zero :
    FiberBundle
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E) 𝕜)
      (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => TangentSpace I x) 𝕜) :=
     inferInstanceAs <| FiberBundle
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E) 𝕜)
      (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E) 𝕜)

noncomputable instance tensor0S_vectorBundle_zero :
    VectorBundle 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E) 𝕜)
      (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => TangentSpace I x) 𝕜) :=
     inferInstanceAs <| VectorBundle 𝕜
       (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E) 𝕜)
        (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E) 𝕜)

noncomputable instance tensor0S_contMDiffVectorBundle_zero :
    ContMDiffVectorBundle n
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E) 𝕜)
      (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => TangentSpace I x) 𝕜) I :=
    inferInstanceAs <| ContMDiffVectorBundle n
       (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E) 𝕜)
       (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E) 𝕜) I

structure Tensor0SBundleData (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (H : Type*) [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (n : WithTop ℕ∞) [IsManifold I n M]
    (s : ℕ) where
  topology : TopologicalSpace (TotalSpace
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
    (fun x : M => Tensor0SSpace s I x))
  fiber : FiberBundle
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
    (fun x : M => Tensor0SSpace s I x)
  vector : VectorBundle 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
    (fun x : M => Tensor0SSpace s I x)
  smooth : ContMDiffVectorBundle n
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
    (fun x : M => Tensor0SSpace s I x) I

noncomputable def tensor0SBundleData_zero :
    Tensor0SBundleData (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) 0 := {
  topology := tensor0S_topologicalSpace_zero
  fiber := tensor0S_fiberBundle_zero
  vector := tensor0S_vectorBundle_zero
  smooth := inferInstanceAs <| ContMDiffVectorBundle n
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E) 𝕜)
    (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E) 𝕜) I
}

noncomputable instance tensor0SBundleData : (s : ℕ) →
    Tensor0SBundleData (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
  | 0 => tensor0SBundleData_zero  (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n)
  | s + 1 => by
    let prev := tensor0SBundleData s
    refine {
      topology := ?_,
      fiber := ?_,
      vector := ?_,
      smooth := ?_
    }
    · have h : (fun x : M => Tensor0SSpace (s+1) I x) =
              (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin (s+1) => E) 𝕜) := by
        ext x
        unfold Tensor0SSpace
        unfold TangentSpace
        rfl
      rw [h]
      infer_instance
    · exact inferInstanceAs <| FiberBundle
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin (s+1) => E) 𝕜)
        (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin (s+1) => E) 𝕜)
    · exact inferInstanceAs <| VectorBundle 𝕜
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin (s+1) => E) 𝕜)
        (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin (s+1) => E) 𝕜)
    · haveI : ContMDiffVectorBundle n E
        (fun x : M => TangentSpace I x) I := inferInstance
      exact inferInstanceAs <| ContMDiffVectorBundle n
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin (s+1) => E) 𝕜)
        (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin (s+1) => E) 𝕜) I

instance tensor0SBundle_topology (s : ℕ) :
    TopologicalSpace (TotalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
      (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => TangentSpace I x) 𝕜)) :=
  (tensor0SBundleData n s).topology

@[simp]
noncomputable instance tensor0SBundle_fiber (s : ℕ) :
    @FiberBundle
      M
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
      _
      _
      (fun x : M => Tensor0SSpace s I x)
      (tensor0SBundle_topology (n := n) s)
      _
      :=
  (@tensor0SBundleData 𝕜 _ E _ _ _ H _ I M _ _ n _ s).fiber

@[simp]
noncomputable instance tensor0SBundle_vector (s : ℕ) :
    @VectorBundle
      𝕜
      M
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
      (fun x : M => Tensor0SSpace s I x)
      _
      _
      _
      _
      _
      _
      (tensor0SBundle_topology (n := n) s)
      _
      (tensor0SBundleData n s).fiber
      :=
  (tensor0SBundleData (n := n) s).vector

@[simp]
noncomputable instance tensor0SBundle_smooth (s : ℕ) :
    @ContMDiffVectorBundle
      n
      𝕜
      M
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
      (fun x : M => Tensor0SSpace s I x)
      _
      E
      _
      _
      H
      _
      I
      _
      _
      _
      _
      _
      _
      (tensor0SBundle_topology (n := n) s)
      _
      (tensor0SBundleData n s).fiber
      (tensor0SBundleData n s).vector
      :=
  (tensor0SBundleData (n := n) s).smooth

#check tensor0SBundle_smooth n 5

-- Topology for (r,s)-tensor bundles as Hom((0,r), (0,s))
noncomputable instance tensorRSBundle_topology (r s : ℕ) :
    TopologicalSpace (TotalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
      (fun x : M => Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x)) := by
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensor0SBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensor0SBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensor0SBundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensor0SBundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    exact Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜)
      (fun (x : M) => ContinuousMultilinearMap 𝕜 (fun _ : Fin r => TangentSpace I x) 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
      (fun (x : M) => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => TangentSpace I x) 𝕜)

#check (tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) 5 6)

-- Fiber bundle instance for (r,s)-tensors
noncomputable instance tensorRSBundle_fiber (r s : ℕ) :
    @FiberBundle
      M
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
      _
      (by infer_instance : TopologicalSpace _)
      (fun x : M => ContinuousMultilinearMap 𝕜 (fun _ : Fin r => TangentSpace I x) 𝕜 →L[𝕜]
        ContinuousMultilinearMap 𝕜 (fun _ : Fin s => TangentSpace I x) 𝕜)
      (tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
      _
      := by
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensor0SBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensor0SBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensor0SBundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensor0SBundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI : ∀ (x : M), IsTopologicalAddGroup (Tensor0SSpace s I x) :=
      fun _ => inferInstance
    letI : ∀ (x : M), ContinuousSMul 𝕜 (Tensor0SSpace s I x) :=
      fun _ => inferInstance
    exact Bundle.ContinuousLinearMap.fiberBundle (RingHom.id 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜)
      (fun (x : M) => Tensor0SSpace r I x)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
      (fun (x : M) => Tensor0SSpace s I x)

-- Vector bundle instance for (r,s)-tensors

noncomputable instance tensorRSBundle_vector (r s : ℕ) :
    @VectorBundle
      𝕜
      M
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
      (fun x : M => Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x)
      _  -- [NontriviallyNormedField 𝕜]
      (fun x => by infer_instance)  -- [∀ x, AddCommMonoid (E x)]
      (fun x => by infer_instance)  -- [∀ x, Module 𝕜 (E x)]
      (tensorRSModel_normedAddCommGroup r s)  -- [NormedAddCommGroup F]
      (tensorRSModel_normedSpace r s)         -- [NormedSpace 𝕜 F]
      _  -- [TopologicalSpace M]
      (tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
      _  -- [∀ x, TopologicalSpace (E x)]
      (tensorRSBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
      := by
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensor0SBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensor0SBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensor0SBundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensor0SBundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI : ∀ (x : M), IsTopologicalAddGroup (Tensor0SSpace s I x) :=
      fun _ => inferInstance
    letI : ∀ (x : M), ContinuousSMul 𝕜 (Tensor0SSpace s I x) :=
      fun _ => inferInstance
    exact Bundle.ContinuousLinearMap.vectorBundle (RingHom.id 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜)
      (fun (x : M) => Tensor0SSpace r I x)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
      (fun (x : M) => Tensor0SSpace s I x)

-- Smooth vector bundle instance for (r,s)-tensors

noncomputable instance tensorRSBundle_smooth (r s : ℕ) :
    @ContMDiffVectorBundle
      n
      𝕜
      M
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
      (fun x : M => Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x)
      _
      E
      _
      _
      H
      _
      I
      _
      _
      _
      _
      _
      _
      (tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
      _
      (tensorRSBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
      (tensorRSBundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
      := by
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensor0SBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensor0SBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensor0SBundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensor0SBundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensor0SBundle_smooth (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensor0SBundle_smooth (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI : ∀ (x : M), IsTopologicalAddGroup (Tensor0SSpace s I x) :=
      fun _ => inferInstance
    letI : ∀ (x : M), ContinuousSMul 𝕜 (Tensor0SSpace s I x) :=
      fun _ => inferInstance
    exact ContMDiffVectorBundle.continuousLinearMap





/-We did not specify the tensor field above, but that is just the smooth section-/

/- Product of (0,s) and (0,s') to a (0,s+s') tensor (and r,s and r',s')-/
/- Interior product -/
/- Contraction of (r,s) by a tangent vector to get (r,s-1), or a cotangent vector to get (r-1,s)
tensor-/
/- Lie derivatives based on contraction and Lie bracket on vector field (which is defined already)-/

-- Tensor fields as smooth sections of tensor bundles

def TensorRSField (r s : ℕ) : Type _ :=
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s
  ContMDiffSection I
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜 →L[𝕜]
     ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
    n
    (fun x : M => Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x)



-- Product of (0,s) and (0,q) tensors to give (0,s+q) tensor
noncomputable def tensor0S_product (s q : ℕ) (x : M) :
    Tensor0SSpace s I x →L[𝕜] Tensor0SSpace q I x →L[𝕜] Tensor0SSpace (s + q) I x := by
  sorry


-- Product for general (r,s) tensors
noncomputable def tensorRS_product (r s r' s' : ℕ) (x : M) :
    (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x) →L[𝕜]
    (Tensor0SSpace r' I x →L[𝕜] Tensor0SSpace s' I x) →L[𝕜]
    (Tensor0SSpace (r + r') I x →L[𝕜] Tensor0SSpace (s + s') I x) := by
  sorry

-- Interior product: contraction of a (0,s) tensor with a tangent vector to get (0,s-1)
noncomputable def interior_product (s : ℕ) (x : M)
    (v : TangentSpace I x) :
    Tensor0SSpace (s + 1) I x →L[𝕜] Tensor0SSpace s I x := by
  sorry



-- Contraction of (r,s) tensor with tangent vector to get (r,s-1)
noncomputable def contract_covariant (r s : ℕ) (x : M)
    (v : TangentSpace I x) :
    (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace (s + 1) I x) →L[𝕜]
    (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x) := by
  sorry

-- Contraction of (r,s) tensor with cotangent vector to get (r-1,s)
noncomputable def contract_contravariant (r s : ℕ) (x : M)
    (α : Tensor0SSpace 1 I x) :
    (Tensor0SSpace (r + 1) I x →L[𝕜] Tensor0SSpace s I x) →L[𝕜]
    (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x) := by
  sorry


-- Lie derivative for general (r,s) tensors
noncomputable def lie_derivative_tensorRS (r s : ℕ)
    {V: Π (x : M), TangentSpace I x }
    (hV : ContMDiff I I.tangent n (fun x ↦ (V x : TangentBundle I M)))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s) :
    TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s := by
  sorry
