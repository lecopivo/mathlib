import topology.algebra.group
import topology.algebra.module
import topology.constructions
import analysis.normed_space.basic
import analysis.normed_space.inner_product

structure seminorm (𝕜 : Type*) (E : Type*)
  [normed_field 𝕜] [add_comm_group E] [vector_space 𝕜 E] :=
(to_fun   : E → ℝ)
(smul     : ∀ (a : 𝕜) (x : E), to_fun (a • x) = ∥a∥ * to_fun x)
(triangle : ∀ x y : E, to_fun (x + y) ≤ to_fun x + to_fun y)

namespace seminorm
  variables {𝕜 : Type*} {E : Type*} {ι : Type*} [normed_field 𝕜] [add_comm_group E] [vector_space 𝕜 E]

  instance : has_coe_to_fun (seminorm 𝕜 E) := has_coe_to_fun.mk _ seminorm.to_fun
  
  noncomputable def induce_topology (seminorms : ι → seminorm 𝕜 E) : topological_space E :=
                      ⨅(i : ι), topological_space.induced (seminorms i) (by apply_instance)

end seminorm


class locally_convex_space (𝕜 : Type*) (E : Type*) [normed_field 𝕜] [add_comm_group E] [vector_space 𝕜 E] [τ : topological_space E] : Prop :=
  (seminorms_induce_topology : 
    ∃ (ι : Type) (seminorms : ι → seminorm 𝕜 E), seminorm.induce_topology seminorms = τ)

namespace locally_convex_space
  variables {𝕜 : Type*} (E : Type*)
  variables [normed_field 𝕜]
  variables [add_comm_group E] [vector_space 𝕜 E] [topological_space E] [locally_convex_space 𝕜 E]

  /- add and smul are continuous in the topology induced by seminorms -/
  instance : topological_add_group E := sorry
  instance : topological_vector_space 𝕜 E := sorry

end locally_convex_space

section locally_convex_space
  variables {𝕜 : Type*} {E : Type*} {F : Type*} {ι : Type*}
  variables [normed_field 𝕜] 
  variables [add_comm_group E] [vector_space 𝕜 E] [topological_space E] [locally_convex_space 𝕜 E]
  variables [add_comm_group F] [vector_space 𝕜 F] [topological_space F] [locally_convex_space 𝕜 F]

  instance prod.locally_convex_space : locally_convex_space 𝕜 (E×F) := 
    { seminorms_induce_topology := begin sorry end }

  instance pi.locally_convex_space {E : ι → Type*} [∀ i, add_comm_group (E i)] [∀i, vector_space 𝕜 (E i)]
    [∀ i, topological_space (E i)] [lcs : ∀ i, locally_convex_space 𝕜 (E i)] :
    locally_convex_space 𝕜 (Πi, E i) := sorry
  
  instance submodule.locally_convex_space (s : submodule 𝕜 E) : locally_convex_space 𝕜 s := sorry

  instance normed_space.locally_convex_space {U : Type*} [normed_group U] [normed_space 𝕜 U] : locally_convex_space 𝕜 U := sorry
  
end locally_convex_space

