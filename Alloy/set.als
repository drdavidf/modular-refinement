
open id

module Set

sig Set {
	var items : set ID
}

pred Set_Inv[s:Set]
{
	no none  
}

fun Set_items[s:Set]: set ID
{
	s.items
}

pred Set_Init[s:Set]
{
	no s.items
}

pred Set_Skip[s:Set]
{
	s.items' = s.items
}

pred Set_Add[s:Set, item:ID]
{
	s.items' = s.items + item
}

pred Set_Remove[s:Set, item:ID]
{
	s.items' = s.items - item
}

pred Set_Full[s:Set]
{
	s.items = ID
}

// compatibility

check {
	all c1,c2 : Set, item : ID - NULL | 
		c1 != c2 => {
			{
				Set_Add[c1, item] 
				Set_Remove[c2,item]

			} => Set_Remove[c2,item]
		}
}

check {
	all c1,c2 : Set, item : ID - NULL | 
		c1 != c2 => {
			{
				Set_Add[c1, item] 
				Set_Remove[c2,item]

			} => Set_Add[c1,item]
		}
}
