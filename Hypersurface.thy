section \<open>Hypersurface\<close>
theory Hypersurface
  imports Smooth_Manifolds.Differentiable_Manifold Ordinary_Differential_Equations.ODE_Analysis "HOL-Analysis.Inner_Product"
begin

abbreviation R::real where "R == 1"

abbreviation def_fn where "def_fn == \<lambda>x. (norm x)\<^sup>2 - (R)\<^sup>2 "

abbreviation def_constraint where "def_constraint == \<lambda>x. def_fn x = 0"

(* alternate version? *)
definition defining_function:: "('a::euclidean_space set) \<Rightarrow> real" where
  "\<lambda>x. (norm x)\<^sup>2 - (R)\<^sup>2 "

typedef (overloaded) ('a::real_normed_vector) surface =
  "{a::'a\<times>real. def_constraint a}" 
proof -
  have "(norm (0::'a,R::real))\<^sup>2 - (R)\<^sup>2 = 0" by simp
  then show ?thesis by blast
qed

setup_lifting type_definition_surface

instantiation surface :: (real_normed_vector) topological_space
begin

lift_definition open_surface :: "'a surface set \<Rightarrow> bool" is
  "openin (subtopology (euclidean::('a\<times>real) topology) {a. def_constraint a})" .

instance
  apply standard
  apply (transfer; auto)
  apply (transfer; auto)
  apply (transfer; auto)
  done

end

instance surface :: (real_normed_vector) t2_space
  apply standard
  apply transfer
  subgoal for x y
    apply (drule hausdorff[of x y])
    apply clarsimp
    subgoal for U V
      apply (rule exI[where x="U \<inter> {a. def_constraint a}"])
      apply clarsimp
      apply (rule conjI) defer
       apply (rule exI[where x="V \<inter> {a. def_constraint a}"])
      by auto
    done
  done

instance surface :: (euclidean_space) second_countable_topology
proof standard
  obtain BB::"('a\<times>real) set set" where BB: "countable BB" "open = generate_topology BB"
    by (metis ex_countable_subbasis)
  let ?B = "(\<lambda>B. B \<inter> {x. norm x = R}) ` BB"
  show "\<exists>B::'a surface set set. countable B \<and> open = generate_topology B"
    apply transfer
    apply (rule bexI[where x = ?B])
    apply (rule conjI)
    subgoal using BB by force
    subgoal using BB apply clarsimp
      apply (subst openin_subtopology_eq_generate_topology[where BB=BB])
      by (auto )
    subgoal by auto
    done
      qed

lemma find_chart_around_point:
  fixes s::"'a surface"
  fixes x::"'b::real_normed_vector"
  assumes on_surface: "def_fn x = 0"
  assumes gradient: "def_fn has_derivative f' (at x)"
  assumes nonzero_gradient: "(norm f') \<noteq> 0"
  assumes "VN = subspace f'"
  assumes "VT = subspace {y. orthogonal f' y}"
  obtains chart_around_point 
  where
  "x = xt+xn" "xt \<in> VT \<and> xn \<in> VN",
  "\<And>s. s \<in> cball xt e \<Longrightarrow> f (s, u s) = 0"
  "phi = \<lambda>x. xt"
  "phi_inv = \<lambda>t. (t, u t)"
  "E = cball xt e"
  "U = phi_inv E"
  "chart_around_point \<equiv> (U, E, phi, phi_inv)"
proof 
  have 
    by (rule implicit_function_theorem[OF f' x]; blast)
  sorry
qed

definition charts_surface :: "('a::euclidean_space surface, 'a) chart" where
  "charts_surface \<equiv> {x \<in> surface | find_chart_around_point x}"


lemma transfer_continuous_on1[transfer_rule]:
  includes lifting_syntax
  shows "(rel_set (=) ===> ((=) ===> pcr_surface (=)) ===> (=)) (\<lambda>X::'a::t2_space set. continuous_on X) continuous_on"
  apply (rule continuous_on_transfer_right_total2)
        apply transfer_step
       apply transfer_step
      apply transfer_step
     apply transfer_prover
    apply transfer_step
   apply transfer_step
  apply transfer_prover
  done

lemma transfer_continuous_on2[transfer_rule]:
  includes lifting_syntax
  shows "(rel_set (pcr_surface (=)) ===> (pcr_surface (=) ===> (=)) ===> (=)) (\<lambda>X. continuous_on (X \<inter> {x. def_constraint x})) (\<lambda>X. continuous_on X)"
  apply (rule continuous_on_transfer_right_total)
        apply transfer_step
       apply transfer_step
      apply transfer_step
     apply transfer_prover
    apply transfer_step
   apply transfer_step
  apply transfer_prover
  done
