// Lean compiler output
// Module: Maze.Solver
// Imports: Init Lean
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_IO_FS_Handle_readToEnd___boxed(lean_object*, lean_object*);
static lean_object* l_Solver_callSolver___rarg___closed__1;
static lean_object* l_Solver_callSolver___rarg___closed__8;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_IO_Process_spawn___boxed(lean_object*, lean_object*);
lean_object* l_String_toNat_x21(lean_object*);
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Solver_callSolver___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Solver_callSolver___rarg___lambda__3___closed__1;
lean_object* l_String_trim(lean_object*);
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Solver_callSolver(lean_object*);
static lean_object* l_Solver_callSolver___rarg___closed__3;
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Solver_callSolver___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Solver_callSolver___spec__1(lean_object*);
static lean_object* l_Solver_callSolver___rarg___closed__6;
static lean_object* l_Solver_callSolver___rarg___closed__7;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_flush___boxed(lean_object*, lean_object*);
lean_object* l_IO_Process_Child_wait___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___closed__2;
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Solver_callSolver___rarg___closed__5;
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_putStr___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Solver_callSolver___rarg___closed__2;
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_IO_Process_Child_takeStdin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_splitOn(lean_object*, lean_object*);
static lean_object* l_Solver_callSolver___rarg___closed__4;
static lean_object* _init_l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___lambda__1___closed__1;
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_2(x_9, lean_box(0), x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_11);
return x_12;
}
}
}
static lean_object* _init_l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = l___private_Init_Data_Repr_0__Nat_reprFast(x_10);
x_14 = l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___closed__1;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___closed__2;
x_17 = lean_string_append(x_15, x_16);
lean_inc(x_4);
x_18 = lean_alloc_closure((void*)(l_IO_FS_Handle_putStr___boxed), 3, 2);
lean_closure_set(x_18, 0, x_4);
lean_closure_set(x_18, 1, x_17);
lean_inc(x_3);
x_19 = lean_apply_2(x_3, lean_box(0), x_18);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_20, 0, x_1);
lean_inc(x_2);
x_21 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_19, x_20);
x_22 = lean_alloc_closure((void*)(l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___lambda__2), 6, 5);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_2);
lean_closure_set(x_22, 2, x_3);
lean_closure_set(x_22, 3, x_4);
lean_closure_set(x_22, 4, x_11);
x_23 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_21, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Solver_callSolver___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Solver_callSolver___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_String_toNat_x21(x_5);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_String_toNat_x21(x_9);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
static lean_object* _init_l_Solver_callSolver___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = l_String_trim(x_2);
x_4 = l_Solver_callSolver___rarg___lambda__1___closed__1;
x_5 = l_String_splitOn(x_3, x_4);
x_6 = lean_box(0);
x_7 = l_List_mapTR_loop___at_Solver_callSolver___spec__2(x_5, x_6);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_2(x_9, lean_box(0), x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint32_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_closure((void*)(l_IO_FS_Handle_readToEnd___boxed), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_apply_2(x_2, lean_box(0), x_7);
x_9 = lean_alloc_closure((void*)(l_Solver_callSolver___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_3);
x_10 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
static lean_object* _init_l_Solver_callSolver___rarg___lambda__3___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; 
x_1 = 2;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, 1, x_2);
lean_ctor_set_uint8(x_3, 2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Solver_callSolver___rarg___lambda__3___closed__1;
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l_IO_Process_Child_wait___boxed), 3, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
lean_inc(x_3);
x_9 = lean_alloc_closure((void*)(l_Solver_callSolver___rarg___lambda__2___boxed), 5, 4);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_3);
x_10 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l_IO_Process_Child_takeStdin___boxed), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_inc(x_3);
x_8 = lean_apply_2(x_3, lean_box(0), x_7);
lean_inc(x_5);
x_9 = lean_alloc_closure((void*)(l_Solver_callSolver___rarg___lambda__3), 4, 3);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_4);
lean_closure_set(x_9, 2, x_5);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_alloc_closure((void*)(l_IO_FS_Handle_flush___boxed), 2, 1);
lean_closure_set(x_8, 0, x_1);
lean_inc(x_2);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
lean_inc(x_6);
x_10 = lean_alloc_closure((void*)(l_Solver_callSolver___rarg___lambda__4___boxed), 6, 5);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_5);
lean_closure_set(x_10, 4, x_6);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_box(0);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_9);
lean_inc(x_2);
x_11 = lean_alloc_closure((void*)(l_Solver_callSolver___rarg___lambda__5___boxed), 7, 6);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_6);
lean_closure_set(x_11, 3, x_7);
lean_closure_set(x_11, 4, x_1);
lean_closure_set(x_11, 5, x_2);
x_12 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_12 = l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Solver_callSolver___rarg___lambda__1___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___closed__2;
x_19 = lean_string_append(x_17, x_18);
lean_inc(x_3);
x_20 = lean_alloc_closure((void*)(l_IO_FS_Handle_putStr___boxed), 3, 2);
lean_closure_set(x_20, 0, x_3);
lean_closure_set(x_20, 1, x_19);
lean_inc(x_4);
x_21 = lean_apply_2(x_4, lean_box(0), x_20);
lean_inc(x_6);
x_22 = lean_alloc_closure((void*)(l_Solver_callSolver___rarg___lambda__6___boxed), 8, 7);
lean_closure_set(x_22, 0, x_5);
lean_closure_set(x_22, 1, x_6);
lean_closure_set(x_22, 2, x_4);
lean_closure_set(x_22, 3, x_3);
lean_closure_set(x_22, 4, x_7);
lean_closure_set(x_22, 5, x_8);
lean_closure_set(x_22, 6, x_9);
x_23 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_21, x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_13 = l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Solver_callSolver___rarg___lambda__1___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___closed__2;
x_20 = lean_string_append(x_18, x_19);
lean_inc(x_11);
x_21 = lean_alloc_closure((void*)(l_IO_FS_Handle_putStr___boxed), 3, 2);
lean_closure_set(x_21, 0, x_11);
lean_closure_set(x_21, 1, x_20);
lean_inc(x_3);
x_22 = lean_apply_2(x_3, lean_box(0), x_21);
lean_inc(x_7);
x_23 = lean_alloc_closure((void*)(l_Solver_callSolver___rarg___lambda__7___boxed), 10, 9);
lean_closure_set(x_23, 0, x_4);
lean_closure_set(x_23, 1, x_5);
lean_closure_set(x_23, 2, x_11);
lean_closure_set(x_23, 3, x_3);
lean_closure_set(x_23, 4, x_6);
lean_closure_set(x_23, 5, x_7);
lean_closure_set(x_23, 6, x_8);
lean_closure_set(x_23, 7, x_9);
lean_closure_set(x_23, 8, x_10);
x_24 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_22, x_23);
return x_24;
}
}
static lean_object* _init_l_Solver_callSolver___rarg___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_2, 0, x_1);
lean_ctor_set_uint8(x_2, 1, x_1);
lean_ctor_set_uint8(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Solver_callSolver___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Solver_callSolver___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("./external_solver/solver-demo.py", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Solver_callSolver___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Solver_callSolver___rarg___closed__2;
x_2 = l_Solver_callSolver___rarg___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Solver_callSolver___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Solver_callSolver___rarg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("python3", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Solver_callSolver___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = l_Solver_callSolver___rarg___closed__1;
x_3 = l_Solver_callSolver___rarg___closed__6;
x_4 = l_Solver_callSolver___rarg___closed__4;
x_5 = l_Solver_callSolver___rarg___closed__5;
x_6 = 0;
x_7 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_1);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*5, x_6);
return x_7;
}
}
static lean_object* _init_l_Solver_callSolver___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Solver_callSolver___rarg___closed__7;
x_2 = lean_alloc_closure((void*)(l_IO_Process_spawn___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = l_Solver_callSolver___rarg___closed__8;
lean_inc(x_2);
x_10 = lean_apply_2(x_2, lean_box(0), x_9);
x_11 = l_Solver_callSolver___rarg___closed__1;
lean_inc(x_8);
x_12 = lean_alloc_closure((void*)(l_Solver_callSolver___rarg___lambda__8), 10, 9);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_5);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_6);
lean_closure_set(x_12, 4, x_7);
lean_closure_set(x_12, 5, x_1);
lean_closure_set(x_12, 6, x_8);
lean_closure_set(x_12, 7, x_3);
lean_closure_set(x_12, 8, x_11);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Solver_callSolver(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Solver_callSolver___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Solver_callSolver___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_7 = l_Solver_callSolver___rarg___lambda__2(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Solver_callSolver___rarg___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Solver_callSolver___rarg___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Solver_callSolver___rarg___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Solver_callSolver___rarg___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Solver_callSolver___rarg___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
return x_11;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Maze_Solver(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___lambda__1___closed__1 = _init_l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___lambda__1___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___lambda__1___closed__1);
l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___closed__1 = _init_l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___closed__1);
l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___closed__2 = _init_l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___closed__2();
lean_mark_persistent(l_List_forIn_loop___at_Solver_callSolver___spec__1___rarg___closed__2);
l_Solver_callSolver___rarg___lambda__1___closed__1 = _init_l_Solver_callSolver___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Solver_callSolver___rarg___lambda__1___closed__1);
l_Solver_callSolver___rarg___lambda__3___closed__1 = _init_l_Solver_callSolver___rarg___lambda__3___closed__1();
lean_mark_persistent(l_Solver_callSolver___rarg___lambda__3___closed__1);
l_Solver_callSolver___rarg___closed__1 = _init_l_Solver_callSolver___rarg___closed__1();
lean_mark_persistent(l_Solver_callSolver___rarg___closed__1);
l_Solver_callSolver___rarg___closed__2 = _init_l_Solver_callSolver___rarg___closed__2();
lean_mark_persistent(l_Solver_callSolver___rarg___closed__2);
l_Solver_callSolver___rarg___closed__3 = _init_l_Solver_callSolver___rarg___closed__3();
lean_mark_persistent(l_Solver_callSolver___rarg___closed__3);
l_Solver_callSolver___rarg___closed__4 = _init_l_Solver_callSolver___rarg___closed__4();
lean_mark_persistent(l_Solver_callSolver___rarg___closed__4);
l_Solver_callSolver___rarg___closed__5 = _init_l_Solver_callSolver___rarg___closed__5();
lean_mark_persistent(l_Solver_callSolver___rarg___closed__5);
l_Solver_callSolver___rarg___closed__6 = _init_l_Solver_callSolver___rarg___closed__6();
lean_mark_persistent(l_Solver_callSolver___rarg___closed__6);
l_Solver_callSolver___rarg___closed__7 = _init_l_Solver_callSolver___rarg___closed__7();
lean_mark_persistent(l_Solver_callSolver___rarg___closed__7);
l_Solver_callSolver___rarg___closed__8 = _init_l_Solver_callSolver___rarg___closed__8();
lean_mark_persistent(l_Solver_callSolver___rarg___closed__8);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
