theory Solver
  imports Main
begin

(*** QDIMACS-like data structure / PCNF format ***)
(*
We only store the top level quantifiers since they are required to be alternating in prefix.
Otherwise the encoding is straightforward.  There is however some cases where a formula can be
encoded using the below data structure, but not using QDIMACS:
- There is a quantified variable that does not occur in the matrix.
- There is a quantified variable that occurs multiple times in the matrix.
- The innermost quantified set is universal.
*)

datatype literal = P nat | N nat
type_synonym clause = "literal list"
type_synonym matrix = "clause list"

type_synonym quant_set = "nat \<times> nat list"
type_synonym quant_sets = "quant_set list"
datatype prefix =
UniversalFirst quant_set quant_sets |
ExistentialFirst quant_set quant_sets |
Empty

type_synonym pcnf = "prefix \<times> matrix"

(*** Alternative / Hos C30 format ***)
(*
PROBLEM: A potential problem with the above is that it is difficult (for me) to see how the simple
solver from the project plan could be implemented without making it identical to the definition of
the semantics.
OTHER IDEA: Encode a generic QBF formula.  This will allow us to use semantics directly from the
book.  The solver could then, for example, return `None` (or whatever it is called in Isabelle) if
the formula is not in PCNF.
SUMMARY: Encode any formula, only solve PCNF formulas.
*)

(* generic QBF formula *)
datatype QBF =
Var nat |
Neg QBF |
Conj "QBF list" |
Disj "QBF list" |
Ex nat QBF |
All nat QBF

(*** Semantics based on HoS C30 ***)
(* Substitute a variable for True or False. *)
fun substitute_var :: "nat \<Rightarrow> bool \<Rightarrow> QBF \<Rightarrow> QBF" where
"substitute_var z True (Var z') = (if z = z' then Conj [] else Var z')" |
"substitute_var z False (Var z') = (if z = z' then Disj [] else Var z')" |
"substitute_var z b (Neg qbf) = Neg (substitute_var z b qbf)" |
"substitute_var z b (Conj qbf_list) = Conj (map (substitute_var z b) qbf_list)" |
"substitute_var z b (Disj qbf_list) = Disj (map (substitute_var z b) qbf_list)" |
"substitute_var z b (Ex x qbf) = Ex x (if x = z then qbf else substitute_var z b qbf)" |
"substitute_var z b (All y qbf) = All y (if z = y then qbf else substitute_var z b qbf)"

(* Measures number of QBF constructors in argument, required to show termination of semantics. *)
fun qbf_measure :: "QBF \<Rightarrow> nat" where
"qbf_measure (Var _) = 1" |
"qbf_measure (Neg qbf) = 1 + qbf_measure qbf" |
"qbf_measure (Conj qbf_list) = 1 + sum_list (map qbf_measure qbf_list)" |
"qbf_measure (Disj qbf_list) = 1 + sum_list (map qbf_measure qbf_list)" |
"qbf_measure (Ex _ qbf) = 1 + qbf_measure qbf" |
"qbf_measure (All _ qbf) = 1 + qbf_measure qbf"

(* Substituting a variable does not change the QBF measure. *)
lemma qbf_measure_substitute: "qbf_measure (substitute_var z b qbf) = qbf_measure qbf"
proof (induction qbf)
  case (Var x)
  show "qbf_measure (substitute_var z b (Var x)) = qbf_measure (Var x)"
  proof (cases b)
    case True
    thus ?thesis by simp
  next
    case False
    thus ?thesis by simp
  qed
next
  case (Neg qbf)
  thus "qbf_measure (substitute_var z b (Neg qbf)) = qbf_measure (Neg qbf)" by simp
next
  case (Conj qbf_list)
  thus "qbf_measure (substitute_var z b (Conj qbf_list)) = qbf_measure (Conj qbf_list)"
  proof (induction qbf_list)
    case Nil
    thus "qbf_measure (substitute_var z b (Conj [])) = qbf_measure (Conj [])" by simp
  next
    case (Cons x xs)
    thus "qbf_measure (substitute_var z b (Conj (x # xs))) = qbf_measure (Conj (x # xs))" by simp
  qed
next
  case (Disj qbf_list)
  thus "qbf_measure (substitute_var z b (Disj qbf_list)) = qbf_measure (Disj qbf_list)"
  proof (induction qbf_list)
    case Nil
    thus "qbf_measure (substitute_var z b (Disj [])) = qbf_measure (Disj [])" by simp
  next
    case (Cons x xs)
    thus "qbf_measure (substitute_var z b (Disj (x # xs))) = qbf_measure (Disj (x # xs))" by simp
  qed
next
  case (Ex x qbf)
  thus "qbf_measure (substitute_var z b (QBF.Ex x qbf)) = qbf_measure (QBF.Ex x qbf)" by simp
next
  case (All y qbf)
  thus "qbf_measure (substitute_var z b (QBF.All y qbf)) = qbf_measure (QBF.All y qbf)" by simp
qed

(* The measure of an element in a disjunction/conjunction is less than the measure of the
disjunction/conjunction. *)
lemma qbf_measure_lt_sum_list:
  assumes "z \<in> set qbf_list"
  shows "qbf_measure z < Suc (sum_list (map qbf_measure qbf_list))"
proof -
  obtain left right where "left @ z # right = qbf_list" by (metis assms split_list)
  hence "sum_list (map qbf_measure qbf_list)
        = sum_list (map qbf_measure left) + qbf_measure z + sum_list (map qbf_measure right)"
    by fastforce
  thus "qbf_measure z < Suc (sum_list (map qbf_measure qbf_list))" by simp
qed

function qbf_semantics :: "(nat \<Rightarrow> bool) \<Rightarrow> QBF \<Rightarrow> bool" where
"qbf_semantics I (Var z) = I z" |
"qbf_semantics I (Neg qbf) = (\<not>(qbf_semantics I qbf))" |
"qbf_semantics I (Conj qbf_list) = list_all (qbf_semantics I) qbf_list" |
"qbf_semantics I (Disj qbf_list) = list_ex (qbf_semantics I) qbf_list" |
"qbf_semantics I (Ex x qbf) = ((qbf_semantics I (substitute_var x True qbf))
                              \<or> (qbf_semantics I (substitute_var x False qbf)))" |
"qbf_semantics I (All x qbf) = ((qbf_semantics I (substitute_var x True qbf))
                               \<and> (qbf_semantics I (substitute_var x False qbf)))"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(I,qbf). qbf_measure qbf)")
  by (auto simp add: qbf_measure_substitute qbf_measure_lt_sum_list)

(* Simple tests *)
definition "test_qbf = (All 3 (Conj [Disj [Neg (Var 2), Var 3, Var 1], Disj [Neg (Var 1), Var 2]]))"
value "substitute_var 1 False test_qbf"
value "substitute_var 1 True test_qbf"
value "substitute_var 2 False test_qbf"
value "substitute_var 2 True test_qbf"
value "substitute_var 3 False test_qbf"
value "substitute_var 3 True test_qbf"
value "qbf_semantics (\<lambda>x. False) test_qbf"
value "qbf_semantics ((\<lambda>x. False)(2 := True)) test_qbf"
value "qbf_semantics (((\<lambda>x. False)(2 := True))(1 := True)) test_qbf"

(* Satisfiability *)
definition satisfiable :: "QBF \<Rightarrow> bool" where
"satisfiable qbf = (\<exists>I. qbf_semantics I qbf)"

definition logically_eq :: "QBF \<Rightarrow> QBF \<Rightarrow> bool" where
"logically_eq qbf1 qbf2 = (\<forall>I. qbf_semantics I qbf1 = qbf_semantics I qbf2)"

(*** Conversion functions, left-inverses thereof, and proofs of the left-inverseness. ***)
(* Convert literal *)
fun convert_literal :: "literal \<Rightarrow> QBF" where
"convert_literal (P z) = Var z" |
"convert_literal (N z) = Neg (Var z)"

fun convert_literal_inv :: "QBF \<Rightarrow> literal option" where
"convert_literal_inv (Var z) = Some (P z)" |
"convert_literal_inv (Neg (Var z)) = Some (N z)" |
"convert_literal_inv _ = None"

lemma literal_inv: "convert_literal_inv (convert_literal n) = Some n"
proof (induction rule: convert_literal.induct)
  case (1 z)
  thus "convert_literal_inv (convert_literal (P z)) = Some (P z)" by simp
next
  case (2 z)
  thus "convert_literal_inv (convert_literal (N z)) = Some (N z)" by simp
qed

(*
(* like `sequence . map` == `mapM` in Haskell *)
fun sequence_map :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
"sequence_map f list =
  foldr (\<lambda>el acc. Option.bind (f el) (\<lambda>e. Option.bind acc (\<lambda>a. Some (e # a)))) list (Some [])" 

value "sequence_map convert_literal_inv [Var 2, Var 3, Neg (Var 4)]"
value "sequence_map convert_literal_inv [Var 2, Var 3, Neg (Var 4), Conj []]"
*)
(* like sequence in haskell specialized for option types *)
fun sequence_aux :: "'a option list \<Rightarrow> 'a list \<Rightarrow> 'a list option" where
"sequence_aux [] list = Some list" |
"sequence_aux (Some x # xs) list = sequence_aux xs (x # list)" |
"sequence_aux (None # xs) list = None"

fun sequence :: "'a option list \<Rightarrow> 'a list option" where
"sequence list = map_option rev (sequence_aux list [])"

(* Lemmas that are not needed at the moment: *)
(*lemma sequence_aux_no_None_not_None:
  assumes "list_all (\<lambda>x. x \<noteq> None) xs"
  shows "sequence_aux xs list \<noteq> None" using assms
proof (induction xs arbitrary: list)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  then show "sequence_aux (y # ys) list \<noteq> None"
  proof (cases y)
    case None
    hence False using Cons by simp
    thus ?thesis by simp
  next
    case (Some a)
    hence "sequence_aux (y # ys) list = sequence_aux ys (a # list)" by simp
    thus ?thesis using Cons by simp
  qed
qed

lemma sequence_no_None_not_None: "list_all (\<lambda>x. x \<noteq> None) list \<Longrightarrow> sequence list \<noteq> None"
  using sequence_aux_no_None_not_None by auto*)

lemma list_no_None_ex_list_map_Some:
  assumes "list_all (\<lambda>x. x \<noteq> None) list"
  shows "\<exists>xs. map Some xs = list" using assms
proof (induction list)
  case Nil
  show "\<exists>xs. map Some xs = []" by simp
next
  case (Cons a list)
  from this obtain xs where "map Some xs = list" by fastforce
  moreover from Cons obtain x where "Some x = a" by fastforce
  ultimately have "map Some (x # xs) = a # list" by simp
  thus "\<exists>xs. map Some xs = a # list" by (rule exI)
qed

lemma sequence_aux_content: "sequence_aux (map Some xs) list = Some (rev xs @ list)"
proof (induction xs arbitrary: list)
  case Nil
  show "sequence_aux (map Some []) list = Some (rev [] @ list)" by simp
next
  case (Cons y ys)
  thus "sequence_aux (map Some (y # ys)) list = Some (rev (y # ys) @ list)" by simp
qed

lemma sequence_content: "sequence (map Some xs) = Some xs"
proof -
  have "sequence (map Some xs) = map_option rev (sequence_aux (map Some xs) [])" by simp
  moreover have "sequence_aux (map Some xs) [] = Some (rev xs @ [])"
    using sequence_aux_content by fastforce
  ultimately show "sequence (map Some xs) = Some xs" by simp
qed

(* Convert clause *)
fun convert_clause :: "clause \<Rightarrow> QBF" where
"convert_clause cl = Disj (map convert_literal cl)"

fun convert_clause_inv :: "QBF \<Rightarrow> clause option" where
"convert_clause_inv (Disj list) = sequence (map convert_literal_inv list)" |
"convert_clause_inv _ = None"

lemma clause_inv: "convert_clause_inv (convert_clause cl) = Some cl"
proof -
  let ?list = "map convert_literal_inv (map convert_literal cl)"
  have "\<forall>x \<in> set cl. convert_literal_inv (convert_literal x) = Some x" using literal_inv by simp
  hence "map Some cl = ?list" using list_no_None_ex_list_map_Some by fastforce
  hence "sequence ?list = Some cl" using sequence_content by metis
  thus "convert_clause_inv (convert_clause cl) = Some cl" by simp
qed

(* Convert matrix *)
fun convert_matrix :: "matrix \<Rightarrow> QBF" where
"convert_matrix matrix = Conj (map convert_clause matrix)"

fun convert_matrix_inv :: "QBF \<Rightarrow> matrix option" where
"convert_matrix_inv (Conj list) = sequence (map convert_clause_inv list)" |
"convert_matrix_inv _ = None"

lemma matrix_inv: "convert_matrix_inv (convert_matrix mat) = Some mat"
proof -
  let ?list = "map convert_clause_inv (map convert_clause mat)"
  have "\<forall>x \<in> set mat. convert_clause_inv (convert_clause x) = Some x" using clause_inv by simp
  hence "map Some mat = ?list" using list_no_None_ex_list_map_Some by fastforce
  hence "sequence ?list = Some mat" using sequence_content by metis
  thus "convert_matrix_inv (convert_matrix mat) = Some mat" by simp
qed

(* Convert prefix *)
(* Length of quantifier set, used to show termination of convert. *)
fun q_length :: "'a \<times> 'a list \<Rightarrow> nat" where
"q_length (x, xs) = 1 + length xs"

(* Measure length of all quantifier sets in prefix, used to show termination of convert. *)
fun measure_prefix_length :: "pcnf \<Rightarrow> nat" where
"measure_prefix_length (Empty, _) = 0" |
"measure_prefix_length (UniversalFirst q qs, _) = q_length q + sum_list (map q_length qs)" |
"measure_prefix_length (ExistentialFirst q qs, _) = q_length q + sum_list (map q_length qs)"

(* Convert a pcnf formula to a QBF formula. A left-inverse exists, see theorem convert_inv. *)
function convert :: "pcnf \<Rightarrow> QBF" where
"convert (Empty, matrix) = convert_matrix matrix" |
"convert (UniversalFirst (x, []) [], matrix) = All x (convert (Empty, matrix))" |
"convert (ExistentialFirst (x, []) [], matrix) = Ex x (convert (Empty, matrix))" |
"convert (UniversalFirst (x, []) (q # qs), matrix) =
  All x (convert (ExistentialFirst q qs, matrix))" |
"convert (ExistentialFirst (x, []) (q # qs), matrix) =
  Ex x (convert (UniversalFirst q qs, matrix))" |
"convert (UniversalFirst (x, y # ys) qs, matrix) =
  All x (convert (UniversalFirst (y, ys) qs, matrix))" |
"convert (ExistentialFirst (x, y # ys) qs, matrix) =
  Ex x (convert (ExistentialFirst (y, ys) qs, matrix))"
  by pat_completeness auto
termination
  by (relation "measure measure_prefix_length") auto

(* Add universal quantifier to front of pcnf formula. *)
fun add_universal_to_front :: "nat \<Rightarrow> pcnf \<Rightarrow> pcnf" where
"add_universal_to_front x (Empty, matrix) = (UniversalFirst (x, []) [], matrix)" |
"add_universal_to_front x (UniversalFirst (y, ys) qs, matrix) =
  (UniversalFirst (x, y # ys) qs, matrix)" |
"add_universal_to_front x (ExistentialFirst (y, ys) qs, matrix) =
  (UniversalFirst (x, []) ((y, ys) # qs), matrix)"

(* Add existential quantifier to front of pcnf formula. *)
fun add_existential_to_front :: "nat \<Rightarrow> pcnf \<Rightarrow> pcnf" where
"add_existential_to_front x (Empty, matrix) = (ExistentialFirst (x, []) [], matrix)" |
"add_existential_to_front x (ExistentialFirst (y, ys) qs, matrix) =
  (ExistentialFirst (x, y # ys) qs, matrix)" |
"add_existential_to_front x (UniversalFirst (y, ys) qs, matrix) =
  (ExistentialFirst (x, []) ((y, ys) # qs), matrix)"

(* Left-inverse for convert, see theorem convert_inv. *)
fun convert_inv :: "QBF \<Rightarrow> pcnf option" where
"convert_inv (All x qbf) = map_option (\<lambda>p. add_universal_to_front x p) (convert_inv qbf)" |
"convert_inv (Ex x qbf) = map_option (\<lambda>p. add_existential_to_front x p) (convert_inv qbf)" |
"convert_inv qbf = map_option (\<lambda>m. (Empty, m)) (convert_matrix_inv qbf)"

lemma convert_add_all: "convert (add_universal_to_front x pcnf) = All x (convert pcnf)"
  by (induction rule: add_universal_to_front.induct) auto

lemma convert_add_ex: "convert (add_existential_to_front x pcnf) = Ex x (convert pcnf)"
  by (induction rule: add_existential_to_front.induct) auto

(*
(* Lemmas that are not needed at the moment *)
lemma add_all_inv:
  assumes "convert_inv (convert pcnf) = Some pcnf"
  shows "convert_inv (convert (add_universal_to_front x pcnf))
        = Some (add_universal_to_front x pcnf)"
  using assms convert_add_all by simp

lemma add_ex_inv:
  assumes "convert_inv (convert pcnf) = Some pcnf"
  shows "convert_inv (convert (add_existential_to_front x pcnf))
        = Some (add_existential_to_front x pcnf)"
  using assms convert_add_ex by simp
*)

(* convert_inv is a left-inverse of convert *)
theorem convert_inv: "convert_inv (convert pcnf) = Some pcnf"
proof (induction pcnf)
  case (Pair prefix matrix)
  show "convert_inv (convert (prefix, matrix)) = Some (prefix, matrix)"
  proof (induction rule: convert.induct)
    case (1 matrix)
    show "convert_inv (convert (Empty, matrix)) = Some (Empty, matrix)"
      using matrix_inv by simp
  next
    case (2 x matrix)
    show "convert_inv (convert (UniversalFirst (x, []) [], matrix))
         = Some (UniversalFirst (x, []) [], matrix)"
      using matrix_inv by simp
  next
    case (3 x matrix)
    show "convert_inv (convert (ExistentialFirst (x, []) [], matrix))
         = Some (ExistentialFirst (x, []) [], matrix)"
      using matrix_inv by simp
  next
    case (4 x q qs matrix)
    moreover have "add_universal_to_front x (ExistentialFirst q qs, matrix)
                  = (UniversalFirst (x, []) (q # qs), matrix)"
      by (induction q) simp
    ultimately show "convert_inv (convert (UniversalFirst (x, []) (q # qs), matrix))
                    = Some (UniversalFirst (x, []) (q # qs), matrix)"
      by simp
  next
    case (5 x q qs matrix)
    moreover have "add_existential_to_front x (UniversalFirst q qs, matrix)
                  = (ExistentialFirst (x, []) (q # qs), matrix)"
      by (induction q) simp
    ultimately show "convert_inv (convert (ExistentialFirst (x, []) (q # qs), matrix))
                    = Some (ExistentialFirst (x, []) (q # qs), matrix)"
      by simp
  next
    case (6 x y ys qs matrix)
    moreover have "add_universal_to_front x (ExistentialFirst (y, ys) qs, matrix)
                  = (UniversalFirst (x, []) ((y, ys) # qs), matrix)"
      by simp
    ultimately show "convert_inv (convert (UniversalFirst (x, y # ys) qs, matrix))
                    = Some (UniversalFirst (x, y # ys) qs, matrix)"
      by simp
  next
    case (7 x y ys qs matrix)
    moreover have "add_existential_to_front x (UniversalFirst (y, ys) qs, matrix)
                  = (ExistentialFirst (x, []) ((y, ys) # qs), matrix)"
      by simp
    ultimately show "convert_inv (convert (ExistentialFirst (x, y # ys) qs, matrix))
                    = Some (ExistentialFirst (x, y # ys) qs, matrix)"
      by simp
  qed    
qed

(* Corollary: convert is injective. *)
theorem convert_injective: "inj convert"
  apply (rule inj_on_inverseI[where ?g = "the \<circ> convert_inv"])
  by (simp add: convert_inv)

(*** Predicates ***)
(* Is the QBF a literal? *)
fun literal_p :: "QBF \<Rightarrow> bool" where
"literal_p (Var _) = True" |
"literal_p (Neg (Var _)) = True" |
"literal_p _ = False"

(* Is the QBF a clause? *)
fun clause_p :: "QBF \<Rightarrow> bool" where
"clause_p (Disj list) = list_all literal_p list" |
"clause_p _ = False"

(* Is the QBF in conjunctive normal form? *)
fun cnf_p :: "QBF \<Rightarrow> bool" where
"cnf_p (Conj list) = list_all clause_p list" |
"cnf_p _ = False"

(* Is the QBF in prenex normal form with a conjunctive normal form matrix? *)
fun pcnf_p :: "QBF \<Rightarrow> bool" where
"pcnf_p (Ex _ qbf) = pcnf_p qbf" |
"pcnf_p (All _ qbf) = pcnf_p qbf" |
"pcnf_p (Conj list) = cnf_p (Conj list)" |
"pcnf_p _ = False"

(*** Proofs that predicates hold after conversion. ***)
lemma convert_literal_p: "literal_p (convert_literal lit)"
  by (cases lit) auto

lemma convert_clause_p: "clause_p (convert_clause cl)"
  using convert_literal_p by (induction cl) auto

lemma convert_cnf_p: "cnf_p (convert_matrix mat)"
  using convert_clause_p by (induction mat) auto

theorem convert_pcnf_p: "pcnf_p (convert pcnf)"
  using convert_cnf_p by (induction rule: convert.induct) auto

(*** Proofs that there is a pcnf formula yielding any pcnf_p QBF formula ***)
lemma convert_literal_p_ex:
  assumes "literal_p lit"
  shows "\<exists>l. convert_literal l = lit"
proof -
  have "\<exists>l. convert_literal l = Var x" for x using convert_literal.simps by blast
  moreover have "\<exists>l. convert_literal l = Neg (Var x)" for x using convert_literal.simps by blast
  ultimately show "\<exists>l. convert_literal l = lit"
    using assms by (induction rule: literal_p.induct) auto
qed

lemma convert_clause_p_ex:
  assumes "clause_p cl"
  shows "\<exists>c. convert_clause c = cl"
proof -
  from assms obtain xs where 0: "Disj xs = cl" by (metis clause_p.elims(2))
  hence "list_all literal_p xs" using assms by fastforce  
  hence "\<exists>ys. map convert_literal ys = xs" using convert_literal_p_ex
  proof (induction xs)
    case Nil
    show "\<exists>ys. map convert_literal ys = []" by simp
  next
    case (Cons x xs)
    from this obtain ys where "map convert_literal ys = xs" by fastforce
    moreover from Cons convert_literal_p_ex obtain y where "convert_literal y = x" by fastforce
    ultimately have "map convert_literal (y # ys) = x # xs" by simp
    thus "\<exists>ys. map convert_literal ys = x # xs" by (rule exI)
  qed
  thus "\<exists>c. convert_clause c = cl" using 0 by fastforce
qed

lemma convert_cnf_p_ex:
  assumes "cnf_p mat"
  shows "\<exists>m. convert_matrix m = mat"
proof -
  from assms obtain xs where 0: "Conj xs = mat" by (metis cnf_p.elims(2))
  hence "list_all clause_p xs" using assms by fastforce
  hence "\<exists>ys. map convert_clause ys = xs" using convert_clause_p_ex
  proof (induction xs)
    case Nil
    show "\<exists>ys. map convert_clause ys = []" by simp
  next
    case (Cons x xs)
    from this obtain ys where "map convert_clause ys = xs" by fastforce
    moreover from Cons convert_literal_p_ex obtain y where "convert_clause y = x" by fastforce
    ultimately have "map convert_clause (y # ys) = x # xs" by simp
    thus "\<exists>ys. map convert_clause ys = x # xs" by (rule exI)
  qed
  thus "\<exists>m. convert_matrix m = mat" using 0 by fastforce
qed

theorem convert_pcnf_p_ex:
  assumes "pcnf_p qbf"
  shows "\<exists>pcnf. convert pcnf = qbf" using assms
proof (induction qbf)
  case (Var x)
  hence False by simp
  thus ?case by simp
next
  case (Neg qbf)
  hence False by simp
  thus ?case by simp
next
  case (Conj x)
  hence "cnf_p (Conj x)" by simp
  from this obtain m where "convert_matrix m = Conj x" using convert_cnf_p_ex by blast
  hence "convert (Empty, m) = Conj x" by simp
  thus "\<exists>pcnf. convert pcnf = Conj x" by (rule exI)
next
  case (Disj x)
  hence False by simp
  thus ?case by simp
next
  case (Ex x1a qbf)
  from this obtain pcnf where "convert pcnf = qbf" by fastforce
  hence "convert (add_existential_to_front x1a pcnf) = Ex x1a qbf" using convert_add_ex by simp
  thus "\<exists>pcnf. convert pcnf = QBF.Ex x1a qbf" by (rule exI)
next
  case (All x1a qbf)
  from this obtain pcnf where "convert pcnf = qbf" by fastforce
  hence "convert (add_universal_to_front x1a pcnf) = All x1a qbf" using convert_add_all by simp
  thus "\<exists>pcnf. convert pcnf = QBF.All x1a qbf" by (rule exI)
qed

(* range of convert *)
theorem convert_range: "range convert = {p. pcnf_p p}"
  using convert_pcnf_p convert_pcnf_p_ex by blast

(* convert bijective on pcnf_p subset of QBF *)
theorem convert_bijective_on: "bij_betw convert UNIV {p. pcnf_p p}"
  by (simp add: bij_betw_def convert_injective convert_range)

(*** Free Variables ***)
fun free_variables_aux :: "nat set \<Rightarrow> QBF \<Rightarrow> nat list" where
"free_variables_aux bound (Var x) = (if x \<in> bound then [] else [x])" |
"free_variables_aux bound (Neg qbf) = free_variables_aux bound qbf" |
"free_variables_aux bound (Conj list) = concat (map (free_variables_aux bound) list)" |
"free_variables_aux bound (Disj list) = concat (map (free_variables_aux bound) list)" |
"free_variables_aux bound (Ex x qbf) = free_variables_aux (insert x bound) qbf" |
"free_variables_aux bound (All x qbf) = free_variables_aux (insert x bound) qbf"

fun free_variables :: "QBF \<Rightarrow> nat list" where
"free_variables qbf = sort (remdups (free_variables_aux {} qbf))"

lemma bound_subtract_symmetry:
  "set (free_variables_aux (bound \<union> new) qbf) = set (free_variables_aux bound qbf) - new"
  by (induction bound qbf rule: free_variables_aux.induct) auto

(*** Existential Closure ***)
fun existential_closure_aux :: "QBF \<Rightarrow> nat list \<Rightarrow> QBF" where
"existential_closure_aux qbf Nil = qbf" |
"existential_closure_aux qbf (Cons x xs) = Ex x (existential_closure_aux qbf xs)"

fun existential_closure :: "QBF \<Rightarrow> QBF" where
"existential_closure qbf = existential_closure_aux qbf (free_variables qbf)"

lemma ex_closure_vars_not_free:
  "set (free_variables (existential_closure_aux qbf vars)) = set (free_variables qbf) - set vars"
proof (induction qbf vars rule: existential_closure_aux.induct)
  case (1 qbf)
  then show ?case by simp
next
  case (2 qbf x xs)
  let ?close_xs = "existential_closure_aux qbf xs"
  have "set (free_variables_aux {x} ?close_xs) = set (free_variables_aux {} ?close_xs) - {x}"
    using bound_subtract_symmetry[of "{}" "{x}" ?close_xs] by simp
  thus ?case using 2 by auto
qed

theorem ex_closure_no_free: "free_variables (existential_closure qbf) = []"
proof -
  have "set (free_variables (existential_closure_aux qbf (free_variables qbf))) = {}"
    using ex_closure_vars_not_free by simp
  thus ?thesis by simp
qed

lemma swap_substitute_var_order:
  assumes "x1 \<noteq> x2 \<or> b1 = b2"
  shows "substitute_var x1 b1 (substitute_var x2 b2 qbf)
        = substitute_var x2 b2 (substitute_var x1 b1 qbf)"
proof (induction qbf)
  case (Var x)
  show ?case
  proof (cases b2)
    case True
    then show ?thesis using assms by (cases b1) auto
  next
    case False
    then show ?thesis using assms by (cases b1) auto
  qed
next
  case (Neg qbf)
  then show ?case by simp
next
  case (Conj x)
  then show ?case by simp
next
  case (Disj x)
  then show ?case by simp
next
  case (Ex x1a qbf)
  then show ?case by simp
next
  case (All x1a qbf)
  then show ?case by simp
qed

lemma remove_outer_substitute_var:
  assumes "x1 = x2"
  shows "substitute_var x1 b1 (substitute_var x2 b2 qbf) = (substitute_var x2 b2 qbf)" using assms
proof (induction qbf)
  case (Var x)
  show ?case
  proof (cases b2)
    case True
    then show ?thesis using assms by (cases b1) auto
  next
    case False
    then show ?thesis using assms by (cases b1) auto
  qed
next
  case (Neg qbf)
  thus ?case by simp
next
  case (Conj x)
  thus ?case by simp
next
  case (Disj x)
  thus ?case by simp
next
  case (Ex x1a qbf)
  thus ?case by simp
next
  case (All x1a qbf)
  thus ?case by simp
qed

lemma qbf_semantics_substitute_eq_assign:
  "qbf_semantics I (substitute_var x b qbf) \<longleftrightarrow> qbf_semantics (I(x := b)) qbf"
proof (induction "I(x := b)" qbf rule: qbf_semantics.induct)
  case (1 z)
  then show ?case by (cases b) auto
next
  case (2 qbf)
  then show ?case by simp
next
  case (3 qbf_list)
  then show ?case by (induction qbf_list) auto
next
  case (4 qbf_list)
  then show ?case by (induction qbf_list) auto
next
  case (5 x' qbf)
  thus ?case by (cases "x' = x")
                (auto simp add: swap_substitute_var_order remove_outer_substitute_var)
next
  case (6 x' qbf)
  thus ?case by (cases "x' = x")
                (auto simp add: swap_substitute_var_order remove_outer_substitute_var)
qed

lemma sat_iff_ex_sat: "satisfiable qbf \<longleftrightarrow> satisfiable (Ex x qbf)"
proof (cases "satisfiable qbf")
  case True
  from this obtain I where I_def: "qbf_semantics I qbf" unfolding satisfiable_def by blast
  have "I(x := I x) = I(x := True) \<or> I(x := I x) = I(x := False)" by (cases "I x") auto
  hence "I = I(x := True) \<or> I = I(x := False)" by simp
  hence "qbf_semantics (I(x := True)) qbf \<or> qbf_semantics (I(x := False)) qbf"
    using I_def by fastforce
  moreover have "satisfiable (Ex x qbf)
                = (\<exists>I. qbf_semantics (I(x := True)) qbf
                  \<or> qbf_semantics (I(x := False)) qbf)"
    by (simp add: satisfiable_def qbf_semantics_substitute_eq_assign)
  ultimately have "satisfiable (QBF.Ex x qbf)" by blast
  thus ?thesis using True by simp
next
  case False
  thus ?thesis unfolding satisfiable_def using qbf_semantics_substitute_eq_assign by simp
qed

theorem sat_iff_ex_close_sat: "satisfiable qbf \<longleftrightarrow> satisfiable (existential_closure qbf)"
proof -
  have "satisfiable qbf = satisfiable (existential_closure_aux qbf (free_variables qbf))"
  proof (cases "free_variables qbf")
    case Nil
    thus ?thesis by simp
  next
    case (Cons x xs)
    have "satisfiable qbf = satisfiable (existential_closure_aux qbf (x # xs))"
      using sat_iff_ex_sat by (induction xs) auto
    thus "satisfiable qbf = satisfiable (existential_closure_aux qbf (free_variables qbf))"
      using Cons by simp
  qed
  thus ?thesis by simp
qed

(*** Naive solver ***)

(* quantifier expansion *)
fun list_max :: "nat list \<Rightarrow> nat" where
"list_max Nil = 0" |
"list_max (Cons x xs) = max x (list_max xs)"

fun qbf_quantifier_depth :: "QBF \<Rightarrow> nat" where
"qbf_quantifier_depth (Var x) = 0" |
"qbf_quantifier_depth (Neg qbf) = qbf_quantifier_depth qbf" |
"qbf_quantifier_depth (Conj list) = list_max (map qbf_quantifier_depth list)" |
"qbf_quantifier_depth (Disj list) = list_max (map qbf_quantifier_depth list)" |
"qbf_quantifier_depth (Ex x qbf) = 1 + (qbf_quantifier_depth qbf)" |
"qbf_quantifier_depth (All x qbf) = 1 + (qbf_quantifier_depth qbf)"

lemma qbf_quantifier_depth_substitute:
  "qbf_quantifier_depth (substitute_var z b qbf) = qbf_quantifier_depth qbf"
proof (induction qbf)
  case (Var x)
  show ?case by (cases b) auto
next
  case (Neg qbf)
  thus ?case by simp
next
  case (Conj xs)
  thus ?case by (induction xs) auto
next
  case (Disj xs)
  thus ?case by (induction xs) auto
next
  case (Ex x1a qbf)
  thus ?case by simp
next
  case (All x1a qbf)
  thus ?case by simp
qed

lemma qbf_quantifier_depth_eq_max:
  assumes "\<not>qbf_quantifier_depth z < list_max (map qbf_quantifier_depth qbf_list)"
  and "z \<in> set qbf_list"
  shows "qbf_quantifier_depth z = list_max (map qbf_quantifier_depth qbf_list)" using assms
proof (induction qbf_list)
  case Nil
  hence False by simp
  thus ?case by simp
next
  case (Cons x xs)
  thus "qbf_quantifier_depth z = list_max (map qbf_quantifier_depth (x # xs))"
    by (cases "x = z") auto
qed

function expand_quantifiers :: "QBF \<Rightarrow> QBF" where
"expand_quantifiers (Var x) = (Var x)" |
"expand_quantifiers (Neg qbf) = Neg (expand_quantifiers qbf)" |
"expand_quantifiers (Conj list) = Conj (map expand_quantifiers list)" |
"expand_quantifiers (Disj list) = Disj (map expand_quantifiers list)" |
"expand_quantifiers (Ex x qbf) = (Disj [substitute_var x True (expand_quantifiers qbf),
                                        substitute_var x False (expand_quantifiers qbf)])" |
"expand_quantifiers (All x qbf) = (Conj [substitute_var x True (expand_quantifiers qbf),
                                         substitute_var x False (expand_quantifiers qbf)])"
  by pat_completeness auto
termination
  apply (relation "measures [qbf_quantifier_depth, qbf_measure]")
  by (auto simp add: qbf_quantifier_depth_substitute qbf_quantifier_depth_eq_max)
     (auto simp add: qbf_measure_lt_sum_list)

(* Property 1: no quantifiers after expansion. *)
lemma no_quants_after_expand_quants: "qbf_quantifier_depth (expand_quantifiers qbf) = 0"
proof (induction qbf)
  case (Var x)
  show ?case by simp
next
  case (Neg qbf)
  thus ?case by simp
next
  case (Conj x)
  thus ?case by (induction x) auto
next
  case (Disj x)
  thus ?case by (induction x) auto
next
  case (Ex x1a qbf)
  thus ?case using qbf_quantifier_depth_substitute Ex.IH by simp
next
  case (All x1a qbf)
  thus ?case using qbf_quantifier_depth_substitute All.IH by simp
qed

(* Property 2: semantics invariant under expansion (logical equivalence). *)

lemma semantics_inv_under_expand:
  "qbf_semantics I qbf = qbf_semantics I (expand_quantifiers qbf)"
proof (induction qbf arbitrary: I)
  case (Var x)
  show ?case by force
next
  case (Neg qbf)
  thus ?case by simp
next
  case (Conj x)
  thus ?case by (induction x) auto
next
  case (Disj x)
  thus ?case by (induction x) auto
next
  case (Ex x1a qbf)
  thus "qbf_semantics I (QBF.Ex x1a qbf) = qbf_semantics I (expand_quantifiers (QBF.Ex x1a qbf))"
    using qbf_semantics_substitute_eq_assign by fastforce
next
  case (All x1a qbf)
  thus "qbf_semantics I (QBF.All x1a qbf) = qbf_semantics I (expand_quantifiers (QBF.All x1a qbf))"
    using qbf_semantics_substitute_eq_assign by fastforce
qed

lemma sat_iff_expand_quants_sat: "satisfiable qbf \<longleftrightarrow> satisfiable (expand_quantifiers qbf)"
  unfolding satisfiable_def using semantics_inv_under_expand by simp

(* Property 3: free variables invariant under expansion. *)
lemma set_free_vars_subst_all_eq:
  "set (free_variables (substitute_var x b qbf)) = set (free_variables (All x qbf))"
proof (induction x b qbf rule: substitute_var.induct)
  case (1 z z')
  then show ?case by simp
next
  case (2 z z')
  then show ?case by simp
next
  case (3 z b qbf)
  then show ?case by simp
next
  case (4 z b qbf_list)
  then show ?case by simp
next
  case (5 z b qbf_list)
  then show ?case by simp
next
  case (6 z b x qbf)
  then show ?case
  proof (cases "x = z")
    case True
    thus ?thesis by simp
  next
    case False
    have 0: "set (free_variables_aux (s \<union> {x}) q) = set (free_variables_aux s q) - {x}" for q s
      using bound_subtract_symmetry[where ?new = "{x}"] by simp
    have "set (free_variables (substitute_var z b (QBF.Ex x qbf)))
                   = set (free_variables (substitute_var z b qbf)) - {x}" using 0 False by simp
    also have "... = set (free_variables (QBF.All z qbf)) - {x}" using 6 False by simp
    also have "... = set (free_variables_aux {x, z} qbf)" using 0 by simp
    also have "... = set (free_variables (QBF.All z (QBF.Ex x qbf)))" by simp
    finally show ?thesis .
  qed
next
  case (7 z b y qbf)
  thus ?case
  proof (cases "y = z")
    case True
    thus ?thesis by simp
  next
    case False (* Similar to case "6, False" *)
    thus ?thesis using 7 bound_subtract_symmetry[where ?new = "{y}"] by simp
  qed
qed

lemma set_free_vars_subst_ex_eq:
  "set (free_variables (substitute_var x b qbf)) = set (free_variables (Ex x qbf))"
proof (induction x b qbf rule: substitute_var.induct)
  case (1 z z')
  then show ?case by simp
next
  case (2 z z')
  then show ?case by simp
next
  case (3 z b qbf)
  then show ?case by simp
next
  case (4 z b qbf_list)
  then show ?case by simp
next
  case (5 z b qbf_list)
  then show ?case by simp
next
  case (6 z b x qbf)
  then show ?case
  proof (cases "x = z")
    case True
    thus ?thesis by simp
  next
    case False (* Similar to proof in set_free_vars_subst_all_eq *) 
    thus ?thesis using 6 bound_subtract_symmetry[where ?new = "{x}"] by simp
  qed
next
  case (7 z b y qbf)
  thus ?case
  proof (cases "y = z")
    case True
    thus ?thesis by simp
  next
    case False (* Similar to proof in set_free_vars_subst_all_eq *)
    thus ?thesis using 7 bound_subtract_symmetry[where ?new = "{y}"] by simp
  qed
qed

lemma free_vars_inv_under_expand_quants:
  "set (free_variables (expand_quantifiers qbf)) = set (free_variables qbf)"
proof (induction qbf)
  case (Var x)
  then show ?case by simp
next
  case (Neg qbf)
  then show ?case by simp
next
  case (Conj x)
  then show ?case by fastforce
next
  case (Disj x)
  then show ?case by fastforce
next
  case (Ex x1a qbf)
  have 0: "set (free_variables_aux {x1a} q) = set (free_variables q) - {x1a}"
    for q using bound_subtract_symmetry[where ?new = "{x1a}"] by simp
  have "\<forall>b. set (free_variables (substitute_var x1a b (expand_quantifiers qbf)))
            = set (free_variables (QBF.Ex x1a (expand_quantifiers qbf)))"
    using set_free_vars_subst_ex_eq by simp
  hence "set (free_variables (expand_quantifiers (QBF.Ex x1a qbf)))
                 = set (free_variables_aux {x1a} (expand_quantifiers qbf))" by simp
  also have "... = set (free_variables (expand_quantifiers qbf)) - {x1a}" using 0 by simp
  also have "... = set (free_variables qbf) - {x1a}" using Ex.IH by simp
  also have "... = set (free_variables_aux {x1a} qbf)" using 0 by simp
  also have "... = set (free_variables (QBF.Ex x1a qbf))" by simp
  finally show ?case .
next
  case (All x1a qbf) (* Similar to above *)
  thus ?case using bound_subtract_symmetry[where ?new = "{x1a}"] set_free_vars_subst_all_eq by simp
qed

(* Any formula can be expanded to one with the three properties. *)
fun expand_qbf :: "QBF \<Rightarrow> QBF" where
"expand_qbf qbf = expand_quantifiers (existential_closure qbf)"

(* The 3 properties from quantifier expansion are preserved. *)
lemma sat_iff_expand_qbf_sat: "satisfiable (expand_qbf qbf) \<longleftrightarrow> satisfiable qbf"
  using sat_iff_ex_close_sat sat_iff_expand_quants_sat by simp

lemma expand_qbf_no_free: "set (free_variables (expand_qbf qbf)) = {}"
proof -
  have "set (free_variables (expand_qbf qbf))
                 = set (free_variables (expand_quantifiers (existential_closure qbf)))" by simp
  also have "... = set (free_variables (existential_closure qbf))"
    using free_vars_inv_under_expand_quants by simp
  also have "... = {}" using ex_closure_no_free by simp
  finally show ?thesis .
qed

lemma expand_qbf_no_quants: "qbf_quantifier_depth (expand_qbf qbf) = 0"
  using no_quants_after_expand_quants by simp

(* All qbfs without any quantifiers or free variables can be evaluated. *)
fun eval_qbf :: "QBF \<Rightarrow> bool option" where
"eval_qbf (Var x) = None" |
"eval_qbf (Neg qbf) = map_option (\<lambda>x. \<not>x) (eval_qbf qbf)" |
"eval_qbf (Conj list) = map_option (list_all (\<lambda>x. x = True)) (sequence (map eval_qbf list))" |
"eval_qbf (Disj list) = map_option (list_ex (\<lambda>x. x = True)) (sequence (map eval_qbf list))" |
"eval_qbf (Ex x qbf) = None" |
"eval_qbf (All x qbf) = None"

lemma pred_map_ex: "list_ex Q (map f x) = list_ex (Q \<circ> f) x"
  by (induction x) auto

(* The evaluation implements the semantics. *)
lemma eval_qbf_implements_semantics:
  assumes "set (free_variables qbf) = {}" and "qbf_quantifier_depth qbf = 0"
  shows "eval_qbf qbf = Some (qbf_semantics I qbf)" using assms
proof (induction qbf)
  case (Var x)
  then show ?case by simp
next
  case (Neg qbf)
  then show ?case by simp
next
  case (Conj x)
  have "\<forall>q \<in> set x. eval_qbf q = Some (qbf_semantics I q)" using Conj by (induction x) auto
  thus "eval_qbf (Conj x) = Some (qbf_semantics I (Conj x))"
  proof (induction x)
    case Nil
    show "eval_qbf (Conj []) = Some (qbf_semantics I (Conj []))" by simp
  next
    case (Cons y ys)
    have "map eval_qbf ys = map Some (map (qbf_semantics I) ys)" using Cons by simp
    moreover have "eval_qbf y = Some (qbf_semantics I y)" using Cons.prems by simp
    ultimately have "map eval_qbf (y # ys) = map Some (map (qbf_semantics I) (y # ys))" by simp
    hence "sequence (map eval_qbf (y # ys)) = Some (map (qbf_semantics I) (y # ys))"
      using sequence_content by metis
    hence "eval_qbf (Conj (y # ys))
          = Some (list_all (\<lambda>x. x = True) (map (qbf_semantics I) (y # ys)))"
      by simp
    hence "eval_qbf (Conj (y # ys)) = Some (list_all (qbf_semantics I) (y # ys))"
      by (simp add: fun.map_ident list.pred_map)
    thus "eval_qbf (Conj (y # ys)) = Some (qbf_semantics I (Conj (y # ys)))" by simp
  qed
next
  case (Disj x) (* Similar to previous case *)
  have "\<forall>q \<in> set x. eval_qbf q = Some (qbf_semantics I q)" using Disj by (induction x) auto
  thus "eval_qbf (Disj x) = Some (qbf_semantics I (Disj x))"
  proof (induction x)
    case Nil
    show "eval_qbf (Disj []) = Some (qbf_semantics I (Disj []))" by simp
  next
    case (Cons y ys)
    have "map eval_qbf ys = map Some (map (qbf_semantics I) ys)" using Cons by simp
    moreover have "eval_qbf y = Some (qbf_semantics I y)" using Cons.prems by simp
    ultimately have "map eval_qbf (y # ys) = map Some (map (qbf_semantics I) (y # ys))" by simp
    hence "sequence (map eval_qbf (y # ys)) = Some (map (qbf_semantics I) (y # ys))"
      using sequence_content by metis
    hence "eval_qbf (Disj (y # ys))
          = Some (list_ex (\<lambda>x. x = True) (map (qbf_semantics I) (y # ys)))"
      by simp
    hence "eval_qbf (Disj (y # ys)) = Some (list_ex (qbf_semantics I) (y # ys))"
      by (simp add: fun.map_ident pred_map_ex)
    thus "eval_qbf (Disj (y # ys)) = Some (qbf_semantics I (Disj (y # ys)))" by simp
  qed
next
  case (Ex x1a qbf)
  hence False by simp
  thus ?case by simp
next
  case (All x1a qbf)
  hence False by simp
  thus ?case by simp
qed

(* This can then be used to implement the naive solver ... *)
fun naive_solver :: "QBF \<Rightarrow> bool" where
"naive_solver qbf = the (eval_qbf (expand_qbf qbf))"

(* ...which is correct. *)
theorem naive_solver_correct: "naive_solver qbf \<longleftrightarrow> satisfiable qbf"
proof -
  have "\<forall>I. naive_solver qbf = the (Some (qbf_semantics I (expand_qbf qbf)))"
    using expand_qbf_no_free expand_qbf_no_quants eval_qbf_implements_semantics by simp
  hence "naive_solver qbf = satisfiable (expand_qbf qbf)" unfolding satisfiable_def by simp
  thus "naive_solver qbf = satisfiable qbf" using sat_iff_expand_qbf_sat by simp
qed

value test_qbf
value "existential_closure test_qbf"
value "expand_qbf test_qbf"
value "naive_solver test_qbf"
value "the (convert_inv test_qbf)"
value "the (convert_inv (existential_closure test_qbf))"
value "convert_inv (expand_qbf test_qbf)"


(*lemma semantics_eq_if_free_vars_eq:
  assumes "\<forall>x \<in> set (free_variables qbf). I(x) = J(x)"
  shows "qbf_semantics I qbf = qbf_semantics J qbf" using assms
proof (induction I qbf rule: qbf_semantics.induct)
  case (1 I z)
  then show ?case by simp
next
  case (2 I qbf)
  then show ?case by simp
next
  case (3 I qbf_list)
  then show ?case by (induction qbf_list) auto
next
  case (4 I qbf_list)
  then show ?case by (induction qbf_list) auto
next
  case (5 I x qbf)
  have "qbf_semantics I (substitute_var x True qbf)
       = qbf_semantics J (substitute_var x True qbf)"
    using 5 set_free_vars_subst_ex_eq by blast
  moreover have 1: "qbf_semantics I (substitute_var x False qbf)
                   = qbf_semantics J (substitute_var x False qbf)"
    using 5 set_free_vars_subst_ex_eq by blast
  ultimately show ?case by simp
next
  case (6 I x qbf)
  have "qbf_semantics I (substitute_var x True qbf)
       = qbf_semantics J (substitute_var x True qbf)"
    using 6 set_free_vars_subst_all_eq by blast
  moreover have 1: "qbf_semantics I (substitute_var x False qbf)
                   = qbf_semantics J (substitute_var x False qbf)"
    using 6 set_free_vars_subst_all_eq by blast
  ultimately show ?case by simp
qed*)

end