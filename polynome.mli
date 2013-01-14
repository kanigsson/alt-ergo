(**************************************************************************)
(*                                                                        *)
(*     The Alt-Ergo theorem prover                                        *)
(*     Copyright (C) 2006-2011                                            *)
(*                                                                        *)
(*     Sylvain Conchon                                                    *)
(*     Evelyne Contejean                                                  *)
(*                                                                        *)
(*     Francois Bobot                                                     *)
(*     Mohamed Iguernelala                                                *)
(*     Stephane Lescuyer                                                  *)
(*     Alain Mebsout                                                      *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

open Num

exception Not_a_num
exception Maybe_zero

module type S = sig
  type r 
  val compare : r -> r-> int
  val term_embed : Term.t -> r
  val mult : r -> r -> r
  val print : Format.formatter -> r -> unit
  val abstract_selectors : r -> (r * r) list -> r * (r * r) list
end

module type T = sig

  type r 
  type t
  
  val compare : t -> t -> int
  val hash : t -> int

  val create : (num * r) list -> num -> Ty.t-> t
  val add : t -> t -> t
  val sub : t -> t -> t
  val mult : t -> t -> t
  val mult_const : num -> t -> t
  val div : t -> t -> t * bool
  val modulo : t -> t -> t

  val is_num : t -> num option
  val is_empty : t -> bool
  val find : r -> t -> num
  val choose : t -> num * r
  val subst : r -> t -> t -> t
  val remove : r -> t -> t
  val to_list : t -> (num * r) list * num
    
  val print : Format.formatter -> t -> unit
  val type_info : t -> Ty.t
  val is_monomial : t -> (num * r * num) option

  (* PPMC des denominateurs des coefficients excepte la constante *)
  val ppmc_denominators : t -> num
  (* PGCD des numerateurs des coefficients excepte la constante *)
  val pgcd_numerators : t -> num
  (* retourne un polynome sans constante et sa constante 
     et la constante multiplicative:
     normal_form p = (p',c,d) <=> p = (p' + c) * d *)
  val normal_form : t -> t * num * num
  (* comme normal_form mais le signe est aussi normalise *)
  val normal_form_pos : t -> t * num * num

  val abstract_selectors : t -> (r * r) list -> t * (r * r) list
end

module Make (X : S) : T with type r = X.r
	
