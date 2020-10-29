import topology.constructions
import analysis.convenient_space.curve

namespace convenient 
  open topological_space

  noncomputable def cinf_topology (E : Type*) 
    [add_comm_group E] [vector_space ℝ E] 
    [topological_space E] [locally_convex_space ℝ E] : topological_space E := 
         ⨆(c : smooth_curve E), coinduced c (by apply_instance)

  variables {E : Type*}
  variables [add_comm_group E] [vector_space ℝ E] [topological_space E] [locally_convex_space ℝ E] 
  
  def is_cinf_open (U : set E) : Prop := @is_open _ (cinf_topology E) U

end convenient
