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

open Why_ptree

type env

val file : file -> ((int tdecl, int) annoted * env) list 

val split_goals : 
  ((int tdecl, int) annoted * env) list -> 
  ((int tdecl, int) annoted * env) list list

val term : env -> (Symbols.t * Ty.t) list -> Why_ptree.lexpr -> 
  (int tterm, int) annoted

val new_id : unit -> int
