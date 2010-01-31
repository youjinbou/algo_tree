open Ocamlbuild_plugin;;
open Command;;

dispatch begin function
| After_rules ->
    ocaml_lib ~extern:true ~dir:"+lablGL" "lablgl";
    ocaml_lib ~extern:true ~dir:"+lablGL" "lablglut";
    ocaml_lib ~extern:true ~dir:"+sdl"    "sdl";
    ocaml_lib ~extern:true ~dir:"+sdl"    "sdlcdrom";
(*    ocaml_lib ~extern:true ~dir:"+sdl"    "sdlevent"; *)
    ocaml_lib ~extern:true ~dir:"+sdl"    "sdlgl";
    ocaml_lib ~extern:true ~dir:"+sdl"    "sdljoystick";
    ocaml_lib ~extern:true ~dir:"+sdl"    "sdlkey";
    ocaml_lib ~extern:true ~dir:"+sdl"    "sdlloader"; 
    ocaml_lib ~extern:true ~dir:"+sdl"    "sdlmixer";
    ocaml_lib ~extern:true ~dir:"+sdl"    "sdlmouse";
    ocaml_lib ~extern:true ~dir:"+sdl"    "sdltimer";
    ocaml_lib ~extern:true ~dir:"+sdl"    "sdlttf";
(*    ocaml_lib ~extern:true ~dir:"+sdl"    "sdlvideo"; *)
    ocaml_lib ~extern:true ~dir:"+sdl"    "sdlwm";
    ocaml_lib ~extern:true ~dir:"+oUnit" "oUnit";

| _ -> ()
end;;
