open id
open Set

sig A_S {
	used : Set ,
	free : Set
}

fun Used_items[s:A_S] : set ID
{
	Set_items[s.used]
}

pred Used_Init[s:A_S]
{
	Set_Init[s.used]
}

pred Used_Skip[s:A_S] 
{
	Set_Skip[s.used]
}

pred Used_Add[s:A_S, item:ID] 
{
	Set_Add[s.used, item]
}

pred Used_Remove[s:A_S, item:ID] 
{
	Set_Remove[s.used, item]
}

fun Free_items[s:A_S] : set ID
{
	Set_items[s.free]
}

pred Free_Skip[s:A_S] 
{
	Set_Skip[s.free]
}

pred Free_Init[s:A_S]
{
	Set_Full[s.free] // note the difference with Used_Init
}

pred Free_Add[s:A_S, item:ID] 
{
	Set_Add[s.free,item] 
}

pred Free_Remove[s:A_S, item:ID] 
{
	Set_Remove[s.free,item]
}

// system invariant

pred A_Inv[s:A_S]
{
	no Used_items[s] & Free_items[s]
	Set_Inv[s.used]
	Set_Inv[s.free]
}

//  system operations

pred A_Init[s:A_S]
{
	Used_Init[s]
	Free_Init[s]
}

pred A_acquire[s:A_S, item:ID]
{
	item in Free_items[s]

	Used_Add[s, item]
	Free_Remove[s, item]
}

pred A_release[s:A_S, item:ID]
{
	item in Used_items[s]

	Used_Remove[s, item]
	Free_Add[s, item]
}
	
pred A_dispose[s:A_S, item:ID]
{
	item in Free_items[s]

	Used_Skip[s]
	Free_Remove[s, item]
}

pred A_purchase[s:A_S, item:ID]
{
	item !in Free_items[s]
	item !in Used_items[s]

	Used_Skip[s]
	Free_Add[s, item]
}

fact {

	A_Init[A_S]

	always
	some item : ID | {

		A_acquire[A_S, item] or 
		A_release[A_S, item] or 
		A_dispose[A_S, item] or 
		A_purchase[A_S, item] 
	}

} 

// safety

check {
	always {
		A_Inv[A_S]
	}
} for 3 but 1 A_S

// liveness

run { eventually { # Used_items[A_S] = 3 } } for 3 but 1 A_S



