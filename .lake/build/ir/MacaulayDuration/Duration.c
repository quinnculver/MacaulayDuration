// Lean compiler output
// Module: MacaulayDuration.Duration
// Imports: Init Mathlib Mathlib.Analysis.Calculus.Taylor Mathlib.Analysis.Calculus.Deriv.Basic Mathlib.Analysis.SpecialFunctions.Log.Deriv
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
static lean_object* l_simpleCashFlowSequence___closed__2;
static lean_object* l_cashflowExample22___closed__20;
static lean_object* l_cashflowExample22___closed__1;
static lean_object* l_cashflowExample22___closed__22;
static lean_object* l_simpleCashFlowSequence___closed__3;
LEAN_EXPORT lean_object* l___private_MacaulayDuration_Duration_0__presentValue_match__1_splitter(lean_object*);
static lean_object* l_cashflowExample22___closed__15;
static lean_object* l_cashflowExample22___closed__3;
static lean_object* l_simpleCashFlowSequence___closed__1;
static lean_object* l_cashflowExample22___closed__18;
LEAN_EXPORT lean_object* l___private_MacaulayDuration_Duration_0__presentValue_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_cashflowExample22___closed__6;
static lean_object* l_cashflowExample22___closed__21;
static lean_object* l_cashflowExample22___closed__23;
static lean_object* l_cashflowExample22___closed__17;
static lean_object* l_cashflowExample22___closed__9;
LEAN_EXPORT lean_object* l___private_MacaulayDuration_Duration_0__presentValue_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Mathlib_Data_Real_Basic_0__Real_one;
static lean_object* l_cashflowExample22___closed__27;
static lean_object* l_cashflowExample22___closed__7;
static lean_object* l_cashflowExample22___closed__16;
static lean_object* l_cashflowExample22___closed__19;
static lean_object* l_cashflowExample22___closed__13;
static lean_object* l_cashflowExample22___closed__5;
LEAN_EXPORT lean_object* l_simpleCashFlowSequence;
static lean_object* l_cashflowExample22___closed__30;
static lean_object* l_cashflowExample22___closed__26;
lean_object* l_Nat_cast___at_Real_natCast___spec__2(lean_object*);
static lean_object* l_cashflowExample22___closed__28;
static lean_object* l_cashflowExample22___closed__11;
static lean_object* l_cashflowExample22___closed__29;
static lean_object* l_cashflowExample22___closed__8;
static lean_object* l_cashflowExample22___closed__10;
static lean_object* l_cashflowExample22___closed__14;
static lean_object* l_cashflowExample22___closed__4;
static lean_object* l_cashflowExample22___closed__2;
static lean_object* l_cashflowExample22___closed__24;
LEAN_EXPORT lean_object* l_cashflowExample22;
static lean_object* l_cashflowExample22___closed__12;
static lean_object* l_cashflowExample22___closed__25;
static lean_object* _init_l_simpleCashFlowSequence___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(100u);
x_2 = l_Nat_cast___at_Real_natCast___spec__2(x_1);
return x_2;
}
}
static lean_object* _init_l_simpleCashFlowSequence___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Mathlib_Data_Real_Basic_0__Real_one;
x_2 = l_simpleCashFlowSequence___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_simpleCashFlowSequence___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_simpleCashFlowSequence___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_simpleCashFlowSequence() {
_start:
{
lean_object* x_1; 
x_1 = l_simpleCashFlowSequence___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_MacaulayDuration_Duration_0__presentValue_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_3, x_4, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_MacaulayDuration_Duration_0__presentValue_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_MacaulayDuration_Duration_0__presentValue_match__1_splitter___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_MacaulayDuration_Duration_0__presentValue_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_MacaulayDuration_Duration_0__presentValue_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_cashflowExample22___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1000u);
x_2 = l_Nat_cast___at_Real_natCast___spec__2(x_1);
return x_2;
}
}
static lean_object* _init_l_cashflowExample22___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Mathlib_Data_Real_Basic_0__Real_one;
x_2 = l_cashflowExample22___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_cashflowExample22___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_Nat_cast___at_Real_natCast___spec__2(x_1);
return x_2;
}
}
static lean_object* _init_l_cashflowExample22___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_cashflowExample22___closed__3;
x_2 = l_cashflowExample22___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_cashflowExample22___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Nat_cast___at_Real_natCast___spec__2(x_1);
return x_2;
}
}
static lean_object* _init_l_cashflowExample22___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_cashflowExample22___closed__5;
x_2 = l_cashflowExample22___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_cashflowExample22___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = l_Nat_cast___at_Real_natCast___spec__2(x_1);
return x_2;
}
}
static lean_object* _init_l_cashflowExample22___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_cashflowExample22___closed__7;
x_2 = l_cashflowExample22___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_cashflowExample22___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = l_Nat_cast___at_Real_natCast___spec__2(x_1);
return x_2;
}
}
static lean_object* _init_l_cashflowExample22___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_cashflowExample22___closed__9;
x_2 = l_cashflowExample22___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_cashflowExample22___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = l_Nat_cast___at_Real_natCast___spec__2(x_1);
return x_2;
}
}
static lean_object* _init_l_cashflowExample22___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_cashflowExample22___closed__11;
x_2 = l_cashflowExample22___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_cashflowExample22___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = l_Nat_cast___at_Real_natCast___spec__2(x_1);
return x_2;
}
}
static lean_object* _init_l_cashflowExample22___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_cashflowExample22___closed__13;
x_2 = l_cashflowExample22___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_cashflowExample22___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Nat_cast___at_Real_natCast___spec__2(x_1);
return x_2;
}
}
static lean_object* _init_l_cashflowExample22___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_cashflowExample22___closed__15;
x_2 = l_cashflowExample22___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_cashflowExample22___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = l_Nat_cast___at_Real_natCast___spec__2(x_1);
return x_2;
}
}
static lean_object* _init_l_cashflowExample22___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_cashflowExample22___closed__17;
x_2 = l_cashflowExample22___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_cashflowExample22___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = l_Nat_cast___at_Real_natCast___spec__2(x_1);
return x_2;
}
}
static lean_object* _init_l_cashflowExample22___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_cashflowExample22___closed__19;
x_2 = l_cashflowExample22___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_cashflowExample22___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_cashflowExample22___closed__20;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_cashflowExample22___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_cashflowExample22___closed__18;
x_2 = l_cashflowExample22___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_cashflowExample22___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_cashflowExample22___closed__16;
x_2 = l_cashflowExample22___closed__22;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_cashflowExample22___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_cashflowExample22___closed__14;
x_2 = l_cashflowExample22___closed__23;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_cashflowExample22___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_cashflowExample22___closed__12;
x_2 = l_cashflowExample22___closed__24;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_cashflowExample22___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_cashflowExample22___closed__10;
x_2 = l_cashflowExample22___closed__25;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_cashflowExample22___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_cashflowExample22___closed__8;
x_2 = l_cashflowExample22___closed__26;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_cashflowExample22___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_cashflowExample22___closed__6;
x_2 = l_cashflowExample22___closed__27;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_cashflowExample22___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_cashflowExample22___closed__4;
x_2 = l_cashflowExample22___closed__28;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_cashflowExample22___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_cashflowExample22___closed__2;
x_2 = l_cashflowExample22___closed__29;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_cashflowExample22() {
_start:
{
lean_object* x_1; 
x_1 = l_cashflowExample22___closed__30;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Calculus_Taylor(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Calculus_Deriv_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Log_Deriv(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MacaulayDuration_Duration(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Calculus_Taylor(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Calculus_Deriv_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Log_Deriv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_simpleCashFlowSequence___closed__1 = _init_l_simpleCashFlowSequence___closed__1();
lean_mark_persistent(l_simpleCashFlowSequence___closed__1);
l_simpleCashFlowSequence___closed__2 = _init_l_simpleCashFlowSequence___closed__2();
lean_mark_persistent(l_simpleCashFlowSequence___closed__2);
l_simpleCashFlowSequence___closed__3 = _init_l_simpleCashFlowSequence___closed__3();
lean_mark_persistent(l_simpleCashFlowSequence___closed__3);
l_simpleCashFlowSequence = _init_l_simpleCashFlowSequence();
lean_mark_persistent(l_simpleCashFlowSequence);
l_cashflowExample22___closed__1 = _init_l_cashflowExample22___closed__1();
lean_mark_persistent(l_cashflowExample22___closed__1);
l_cashflowExample22___closed__2 = _init_l_cashflowExample22___closed__2();
lean_mark_persistent(l_cashflowExample22___closed__2);
l_cashflowExample22___closed__3 = _init_l_cashflowExample22___closed__3();
lean_mark_persistent(l_cashflowExample22___closed__3);
l_cashflowExample22___closed__4 = _init_l_cashflowExample22___closed__4();
lean_mark_persistent(l_cashflowExample22___closed__4);
l_cashflowExample22___closed__5 = _init_l_cashflowExample22___closed__5();
lean_mark_persistent(l_cashflowExample22___closed__5);
l_cashflowExample22___closed__6 = _init_l_cashflowExample22___closed__6();
lean_mark_persistent(l_cashflowExample22___closed__6);
l_cashflowExample22___closed__7 = _init_l_cashflowExample22___closed__7();
lean_mark_persistent(l_cashflowExample22___closed__7);
l_cashflowExample22___closed__8 = _init_l_cashflowExample22___closed__8();
lean_mark_persistent(l_cashflowExample22___closed__8);
l_cashflowExample22___closed__9 = _init_l_cashflowExample22___closed__9();
lean_mark_persistent(l_cashflowExample22___closed__9);
l_cashflowExample22___closed__10 = _init_l_cashflowExample22___closed__10();
lean_mark_persistent(l_cashflowExample22___closed__10);
l_cashflowExample22___closed__11 = _init_l_cashflowExample22___closed__11();
lean_mark_persistent(l_cashflowExample22___closed__11);
l_cashflowExample22___closed__12 = _init_l_cashflowExample22___closed__12();
lean_mark_persistent(l_cashflowExample22___closed__12);
l_cashflowExample22___closed__13 = _init_l_cashflowExample22___closed__13();
lean_mark_persistent(l_cashflowExample22___closed__13);
l_cashflowExample22___closed__14 = _init_l_cashflowExample22___closed__14();
lean_mark_persistent(l_cashflowExample22___closed__14);
l_cashflowExample22___closed__15 = _init_l_cashflowExample22___closed__15();
lean_mark_persistent(l_cashflowExample22___closed__15);
l_cashflowExample22___closed__16 = _init_l_cashflowExample22___closed__16();
lean_mark_persistent(l_cashflowExample22___closed__16);
l_cashflowExample22___closed__17 = _init_l_cashflowExample22___closed__17();
lean_mark_persistent(l_cashflowExample22___closed__17);
l_cashflowExample22___closed__18 = _init_l_cashflowExample22___closed__18();
lean_mark_persistent(l_cashflowExample22___closed__18);
l_cashflowExample22___closed__19 = _init_l_cashflowExample22___closed__19();
lean_mark_persistent(l_cashflowExample22___closed__19);
l_cashflowExample22___closed__20 = _init_l_cashflowExample22___closed__20();
lean_mark_persistent(l_cashflowExample22___closed__20);
l_cashflowExample22___closed__21 = _init_l_cashflowExample22___closed__21();
lean_mark_persistent(l_cashflowExample22___closed__21);
l_cashflowExample22___closed__22 = _init_l_cashflowExample22___closed__22();
lean_mark_persistent(l_cashflowExample22___closed__22);
l_cashflowExample22___closed__23 = _init_l_cashflowExample22___closed__23();
lean_mark_persistent(l_cashflowExample22___closed__23);
l_cashflowExample22___closed__24 = _init_l_cashflowExample22___closed__24();
lean_mark_persistent(l_cashflowExample22___closed__24);
l_cashflowExample22___closed__25 = _init_l_cashflowExample22___closed__25();
lean_mark_persistent(l_cashflowExample22___closed__25);
l_cashflowExample22___closed__26 = _init_l_cashflowExample22___closed__26();
lean_mark_persistent(l_cashflowExample22___closed__26);
l_cashflowExample22___closed__27 = _init_l_cashflowExample22___closed__27();
lean_mark_persistent(l_cashflowExample22___closed__27);
l_cashflowExample22___closed__28 = _init_l_cashflowExample22___closed__28();
lean_mark_persistent(l_cashflowExample22___closed__28);
l_cashflowExample22___closed__29 = _init_l_cashflowExample22___closed__29();
lean_mark_persistent(l_cashflowExample22___closed__29);
l_cashflowExample22___closed__30 = _init_l_cashflowExample22___closed__30();
lean_mark_persistent(l_cashflowExample22___closed__30);
l_cashflowExample22 = _init_l_cashflowExample22();
lean_mark_persistent(l_cashflowExample22);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
