(*
#use "boolean_evaluation.ml" ;;
*)


type eb = V of int | TRUE | FALSE | AND of eb * eb |OR of eb * eb |XOR of eb * eb |NOT of eb ;;


let systeme_du_sujet = [OR(V 1, V 2), TRUE; XOR(V 1, V 3), V 2; NOT(AND(V 1, AND(V 2, V 3))), TRUE];;


let test1 = [AND(AND(OR(V 1, V 2), V 2), OR(V 3, V 2)), OR(V 1, V 2)];;


let rec appartient e l =
	match l with
	|[]-> false 
	|(t::q) -> if (t = e) then true
			else appartient e q;;


let rec union l1 l2 =
	match l1,l2 with
	|([],[]) -> []
	|([],t2::q2) -> if (appartient t2 q2) then union [] q2
			else t2::union [] q2  
	|(t1::q1,[]) -> if (appartient t1 q1) then union q1 []
			else t1::union q1 []
	|(t1::q1,t2::q2) -> if ((appartient t1 l2) || (appartient t1 q1)) then union q1 l2 
			else t1::union q1 l2 ;;


let rec det_var_eb eb = 
	match eb with 
	|V(a) -> V(a)::[]
	|TRUE -> []
	|FALSE -> []
	|AND(a, b)-> union (det_var_eb a) (det_var_eb b)
	|OR(a, b) -> union (det_var_eb a) (det_var_eb b)
	|XOR(a, b) -> union (det_var_eb a) (det_var_eb b)
	|NOT(a) -> det_var_eb a;;


	
let rec det_var_sys systeme =
	match systeme with
	|[]->[]
	|(t::q) -> union (union (det_var_eb (fst t)) (det_var_eb (snd t))) (det_var_sys q);;
	
	

let generation e = 
	let rec aux e acc =
		match e with
		|[] -> [acc]
		|(t1::q1) -> let li = (aux q1 (acc @ [(t1, TRUE)])) in
			   let li_deux = (aux q1 (acc @ [(t1, FALSE)])) in
			   li @ li_deux  
	in
	aux e [];;



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
				 else if ((x = TRUE) || (y = TRUE)) then TRUE
				 else if ((x = FALSE) && (y = FALSE)) then FALSE
				 else final_check (XOR(final_check x, final_check y))
	|NOT(x) ->  if (x = TRUE) then FALSE
			    else if (x = FALSE) then TRUE
				else final_check (NOT(final_check x));;



let rec check a b eb =
					match eb with
					|TRUE -> TRUE
					|FALSE -> FALSE
					|V(x) -> if V(x) = a then  b
							else V(x) 
					|OR(x, y) -> if ((x = TRUE) || (y = TRUE)) then TRUE
								 else if ((x = FALSE) && (y = FALSE)) then FALSE
								 else OR(check a b x, check a b y)
					|AND(x, y) -> if ((x = FALSE) || (y = FALSE)) then  FALSE
								 else if ((x = TRUE) && (y = TRUE)) then TRUE
								 else AND(check a b x, check a b y)
					|XOR(x, y) -> if ((x = TRUE) && (y = TRUE)) then FALSE
								 else if ((x = TRUE) || (y = TRUE)) then TRUE
								 else if ((x = FALSE) && (y = FALSE)) then FALSE
								 else XOR(check a b x, check a b y)
					|NOT(x) ->  if (x = TRUE) then FALSE
							    else if (x = FALSE) then TRUE
								else NOT(check a b x);;



let rec eval_expr2 l prop =
		match (l,prop) with 
		|([],_) -> final_check prop
		|((a,b)::q1, prop) -> let remplace = check a b prop in
							if ((remplace = TRUE) || (remplace = FALSE)) then remplace
							else eval_expr2 q1 remplace;;



let rec eval_expr l eb =
		match (l,eb) with
		|(_,[]) -> true
		|(l,(a,b)::q2) -> let che = eval_expr2 l a in
						  let cheki = eval_expr2 l b in 
				if (che = cheki) then eval_expr l q2
				else false;;



let rec evaluation l eb = 
	match (l,eb) with
	|([],[]) -> []
	|([],eb) -> []
	|(t1::q1,eb) -> let checkin = eval_expr t1 eb in
			if checkin = true then t1::evaluation q1 eb
			else evaluation q1 eb;;


let evaluation_sys_eb eb = 
	evaluation (generation (det_var_sys eb)) eb;;


let test = evaluation_sys_eb systeme_du_sujet;;

