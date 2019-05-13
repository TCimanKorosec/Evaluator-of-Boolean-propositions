(*
#use "Evaluateur.ml" ;;


ZHANG Océane 
CIMAN Thomas
*)



(* 
	TYPE POUR LES PROPOSITIONS BOOLEENNES
*)
type eb = V of int | TRUE | FALSE | AND of eb * eb |OR of eb * eb |XOR of eb * eb |NOT of eb ;;



(*

Cette fonction permet de savoir si un élément de type 'a est contenu dans une liste 'a list, le type est donc générique mais
dans ce projet le type sera eb

Le type de sortie de cette fonction est un booléen, si l'élément est contenu renvoi true, sinon false

*)
let rec appartient e l =
	match l with
	|[]-> false 
	|(t::q) -> if (t = e) then true
			else appartient e q;;



(*

Cette fonction prend deux listes génériques en paramètre l1 et l2 et renvoie une liste contenant l'union de ces deux listes

Le type en sorti est donc 'a list et est, dans ce projet une liste contenant tous les V(x) contenus dans la (eb * eb) list 

*)
let rec union l1 l2 =
	match l1,l2 with
	|([],[]) -> []
	|([],t2::q2) -> if (appartient t2 q2) then union [] q2
			else t2::union [] q2  
	|(t1::q1,[]) -> if (appartient t1 q1) then union q1 []
			else t1::union q1 []
	|(t1::q1,t2::q2) -> if ((appartient t1 l2) || (appartient t1 q1)) then union q1 l2 
			else t1::union q1 l2 ;;



(*

Cette fonction prend en paramètre une proposition booléenne, donc de type eb et va permettre d'en sortir les V(x) et de les 
ajouter dans une liste.

Le type de sortie est donc eb list Cette fonction fait appel, évidemment à elle même mais également à la fonction union afin de faire
l'union des V(x) dans une seule liste

*)
let rec det_var_eb eb = 
	match eb with 
	|V(a) -> V(a)::[]
	|TRUE -> []
	|FALSE -> []
	|AND(a, b)-> union (det_var_eb a) (det_var_eb b)
	|OR(a, b) -> union (det_var_eb a) (det_var_eb b)
	|XOR(a, b) -> union (det_var_eb a) (det_var_eb b)
	|NOT(a) -> det_var_eb a;;



(*

Cette fonction prend en paramètre une liste de couple de eb ((eb * eb) list), c'est le système de proposition qu'on veut évaluer. 
Elle va permettre de detecter les V(x) et de les ajouter à une nouvelle liste contenant ainsi tous les V(x) présents dans le système
de propositions booléennes. Elle fait appel à la fonction det_var_eb qui va permettre d'identifier les V(x)

le type de sortie est eb list

*)	
let rec det_var_sys systeme =
	match systeme with
	|[]->[]
	|(t::q) -> union (union (det_var_eb (fst t)) (det_var_eb (snd t))) (det_var_sys q);;
	

	
(*

Cette fonction va générer une liste de liste de V(x) contenant toute les valeurs de vérité TRUE / FALSE possible.
Le nombre de sous liste est égal a 2^n avec n = le nombre de V(x) trouvés dans le système de propositions booléennes

Le type de sortie est donc (eb * eb) list list.

*)
let generation e = 
	let rec aux e acc =
		match e with
		|[] -> [acc]
		|(t1::q1) -> let li = (aux q1 (acc @ [(t1, TRUE)])) in
			   let li_deux = (aux q1 (acc @ [(t1, FALSE)])) in
			   li @ li_deux  
	in
	aux e [];;



(*

Cette fonction permet de faire une check final du système ou les V(x) ont été remplacés par leurs valeurs de vérité dans la 
fonction check. Cette fonction est comme une table de vérité

Le type de sortie est eb et est, au final soit égal à TRUE ou à FALSE

*)
let rec final_check eb =
	match eb with
	|V(x) -> V(x) 
	|TRUE -> TRUE
	|FALSE -> FALSE
	|OR(x, y) -> if ((x = TRUE) || (y = TRUE)) then TRUE
				else if ((x = FALSE) && (y = FALSE)) then FALSE
				else final_check (OR(final_check x, final_check y))
	|AND(x, y) -> if ((x = FALSE) || (y = FALSE)) then  FALSE
				 else if ((x = TRUE) && (y = TRUE)) then TRUE
				 else final_check (AND(final_check x, final_check y))
	|XOR(x, y) -> if ((x = TRUE) && (y = TRUE)) then FALSE
				 else if ((x = FALSE) && (y = FALSE)) then FALSE
				 else if ((x = TRUE) && (y = FALSE)) then TRUE
				 else if ((x = FALSE) && (y = TRUE)) then TRUE
				 else final_check (XOR(final_check x, final_check y))
	|NOT(x) ->  if (x = TRUE) then FALSE
			    else if (x = FALSE) then TRUE
				else final_check (NOT(final_check x));;



(*

Cette fonction prend en paramètre a qui est un V(x), b qui est la valeur de vérité de ce V(x), soit TRUE ou FALSE et eb, une 
proposition booléenne dans laquelle on va remplacer les V(x) (a), par leur valeur de vérité (b)

Le type de sortie est eb et correspond à l'expression booléenne eb passée en paramètre où les V(x) ont été remplacés par leur valeur
de vérité

*)
let rec check a b eb =
					match eb with
					|TRUE -> TRUE
					|FALSE -> FALSE
					|V(x) -> if V(x) = a then b
							else V(x) 
					|OR(x, y) -> if ((x = TRUE) || (y = TRUE)) then TRUE
								 else if ((x = FALSE) && (y = FALSE)) then FALSE
								 else OR(check a b x, check a b y)
					|AND(x, y) -> if ((x = FALSE) || (y = FALSE)) then  FALSE
								 else if ((x = TRUE) && (y = TRUE)) then TRUE
								 else AND(check a b x, check a b y)
					|XOR(x, y) -> if ((x = TRUE) && (y = TRUE)) then FALSE
								 else if ((x = TRUE) && (y = FALSE)) then TRUE
								 else if ((x = FALSE) && (y = TRUE)) then TRUE
								 else if ((x = FALSE) && (y = FALSE)) then FALSE
								 else XOR(check a b x, check a b y)
					|NOT(x) ->  if (x = TRUE) then FALSE
							    else if (x = FALSE) then TRUE
								else NOT(check a b x);;



(*

Cette fonction prend en paramètre une liste de V(x) et un eb à évaluer. elle va appeler la fonction check et stocker le nouveau 
eb dans la variable remplace. Si celle-ci est TRUE ou FALSE on renvoie directement le résultat, sinon on continue avec les autres
V(x) et leurs valeurs de vérité. Lorsqu'il n'y a plus de V(x) dans la liste on fait un check final sur la proposition où tout à
été remplacé

Le type de sorti est eb et sera TRUE ou FALSE

*)
let rec eval_expr2 l prop =
		match (l,prop) with 
		|([],_) -> final_check prop
		|((a,b)::q1, prop) -> let remplace = check a b prop in
							if ((remplace = TRUE) || (remplace = FALSE)) then remplace
							else eval_expr2 q1 remplace;;



(*

Cette fonction prend en prend en paramètre une liste de V(x) (l) ainsi qu'une (eb * eb) list. On va séparer les deux partie de chaque
couple (eb * eb) et appeler eval_expr2 avec chaque eb
Le type de sortie est un booléen. Si dans tous les couples (eb * eb), eb = eb en remplacant les V(x) par leur valeur de vérité, alors
renvoie true pour la liste de V(x) et celle-ci sera ajouter dans le résultat final dans la fonction evaluation

*)
let rec eval_expr l eb =
		match (l,eb) with
		|(_,[]) -> true
		|(l,(a,b)::q2) -> let check_fst = eval_expr2 l a in
						  let check_snd = eval_expr2 l b in 
				if (check_fst = check_snd) then eval_expr l q2
				else false;;



(* 

Cette fonction prend une liste de liste de V(x) avec leurs valeurs de vérité et une liste de proposition booléennes à évaluer
Si la liste de V(x) (t1) est validée avec la liste de propositions eb, alors elle est ajoutée a la liste qui contiendra les ensembles
de V(x) et leur valeur de vérité validées dans la proposition eb

*)
let rec evaluation llVx eb = 
	match (llVx,eb) with
	|([],[]) -> []
	|([],eb) -> []
	|(t1::q1,eb) -> let list_check = eval_expr t1 eb in
			if list_check = true then t1::evaluation q1 eb
			else evaluation q1 eb;;



(*

Fonction prenant une liste de propositions booléennes en paramètre et se servant de toutes les fonctions créees au préalable 
afin d'évaluer quels couple de (V(x), valeur de vérité contenus dans cette expression sont valides

Le type de sortie est une (eb * eb) list list, donc une liste contenant les liste de tous les couple (V(x), valeur de vérité)
validant le systeme eb

*)
let evaluation_sys_eb eb = 
	evaluation (generation (det_var_sys eb)) eb;;


(*
	TESTS
*)


let systeme_du_sujet = [OR(V 1, V 2), TRUE; XOR(V 1, V 3), V 2; NOT(AND(V 1, AND(V 2, V 3))), TRUE];;

let test0 = [AND(TRUE, TRUE), OR(FALSE, TRUE)];;

let test1 = [AND(AND(OR(V 1, V 2), V 2), OR(V 3, V 2)), OR(V 1, V 2)];;

let test2 = [OR(V 1, V 2), XOR(AND(AND(V 1, V 3), AND(V 2, V 3)), V 2)];;

let test3 = [AND(AND(OR(V 1, V 2), V 3), XOR(V 3, V 2)), TRUE] 


let test = evaluation_sys_eb test3;;

