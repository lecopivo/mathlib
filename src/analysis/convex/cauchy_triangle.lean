import analysis.convex.basic
import linear_algebra.affine_space.combination
import data.matrix.notation

noncomputable theory

variables {E : Type*} [add_comm_group E] [vector_space ℝ E] {s : set E}

namespace cauchy_integral

def triangle (PE : Type*) := fin 3 → PE

namespace triangle

open affine_map

variables (t : triangle E)

protected def convex_hull : set E := convex_hull (set.range t)

lemma range_eq : set.range t = {t 0, t 1, t 2} := by simp [triangle]

def split4_homothety : fin 4 → E →ᵃ[ℝ] E :=
![homothety (t 0) (1/2:ℝ), homothety (t 1) (1/2:ℝ), homothety (t 2) (1/2:ℝ),
  homothety (finset.univ.centroid ℝ t) (-1/2:ℝ)]

def split4 : fin 4 → triangle E := λ n, t.split4_homothety n ∘ t

lemma split4_def (i : fin 4) (j : fin 3) :
  t.split4 i j = t.split4_homothety i (t j) :=
rfl



end triangle

end cauchy_integral
