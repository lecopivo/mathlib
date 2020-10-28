import topology.algebra.group
import topology.algebra.module
import topology.constructions
import analysis.normed_space.basic

structure seminorm (𝕜 : Type*) (E : Type*)
  [normed_field 𝕜] [add_comm_group E] [vector_space 𝕜 E] :=
(to_fun   : E → ℝ)
(smul     : ∀ (a : 𝕜) (x : E), to_fun (a • x) = ∥a∥ * to_fun x)
(triangle : ∀ x y : E, to_fun (x + y) ≤ to_fun x + to_fun y)

namespace seminorm
  variables (𝕜 : Type*) (E : Type*) [normed_field 𝕜] [add_comm_group E] [vector_space 𝕜 E]

  instance : has_coe_to_fun (seminorm 𝕜 E) := has_coe_to_fun.mk _ seminorm.to_fun
  
  noncomputable def induce_topology {index_set : Type} (seminorms : index_set → seminorm 𝕜 E) : topological_space E :=
                      ⨅(i : index_set), topological_space.induced (seminorms i) (by apply_instance)
                      /- initial topology is with ⨆ or ⨅? -/

end seminorm

class locally_convex_space (𝕜 : Type*) (E : Type*) 
        [normed_field 𝕜] [τ : topological_space E] [add_comm_group E] 
        [module 𝕜 E] [topological_vector_space 𝕜 E] : Prop
      := 
      (seminorms_induce_topology : ∃ (index_set : Type), ∃ (seminorms : index_set → seminorm 𝕜 E), seminorm.induce_topology seminorms = τ)

