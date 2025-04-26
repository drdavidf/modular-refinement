open id

module chain

sig Chain {
	var first : ID,
	var next : (ID - NULL) /*lone*/ -> /*lone*/ (ID - NULL)
}

fun Chain_items[c : Chain]: set ID
{
	ID.(c.next) + (c.next).ID + c.first - NULL
}

pred Chain_Inv[c : Chain] 
{
	c.next in ID lone -> lone ID

	c.first = NULL => no c.next

	no (c.next).(c.first)

	some (c.next) => 
		(c.first).(*(c.next)) = Chain_items[c]

}

run { Chain_Inv[Chain] } for 3 but 1 Chain

pred Chain_Init[c:Chain]
{
	c.first = NULL
	no c.next 
}

pred Chain_Full[c:Chain]
{
	Chain_Inv[c]
	Chain_items[c] = ID - NULL
}

run { Chain_Full[Chain] } for 3 but 1 Chain, exactly 5 ID

pred Chain_Skip[c:Chain]
{
	c.first' = c.first
	c.next' = c.next
}

pred Chain_Add_ToEmptyChain[c:Chain, item:ID]
{
	c.first = NULL
	item != NULL
	
	c.first' = item
	c.next' = c.next
}

pred Chain_Add_ToNonEmptyChain[c:Chain, item:ID]
{
	c.first != NULL
	item != NULL
	
	c.first' = item
	c.next' = c.next + item -> c.first  
}

pred Chain_Add[c:Chain, item:ID]
{
	item !in Chain_items[c]

	Chain_Add_ToEmptyChain[c, item] or 
	Chain_Add_ToNonEmptyChain[c, item]
}

pred Chain_Remove_Singleton[c:Chain, item :ID]
{
	item != NULL

	c.first = item
	no item.(c.next)

	c.first' = NULL

	no c.next' 
}

pred Chain_Remove_First[c:Chain, item :ID]
{
	item != NULL

	c.first = item
	c.first' = (c.first).(c.next)

	c.next' = (ID - item) <: c.next 
}

pred Chain_Remove_Mid[c:Chain, item :ID]
{
	item != NULL

	some (c.next).item
	some item.(c.next)

	c.first' = c.first

	c.next' = (ID - item) <: c.next :> (ID - item) + 
		(c.next).item -> item.(c.next)
}

pred Chain_Remove_Last[c:Chain, item :ID]
{
	item != NULL

	some (c.next).item
	no item.(c.next)

	c.first' = c.first

	c.next' = c.next :> (ID - item)
}

pred Chain_Remove[c:Chain, item:ID]
{
	Chain_Remove_Singleton[c,item] or
	Chain_Remove_First[c,item] or
	Chain_Remove_Mid[c,item] or
	Chain_Remove_Last[c,item]
}

run { 
	some item : ID |

		Chain_Inv[Chain] and Chain_Remove_Singleton[Chain, item] 
} for 3 but 1 Chain


run { 
	some item : ID |

		Chain_Inv[Chain] and Chain_Remove_First[Chain, item] 
} for 3 but 1 Chain

run { 
	some item : ID |

		Chain_Inv[Chain] and Chain_Remove_Mid[Chain, item] 
} for 4 but 1 Chain

run { 
	some item : ID |

		Chain_Inv[Chain] and Chain_Remove_Last[Chain, item] 
} for 3 but 1 Chain

// compatibility

check {
	all c1,c2 : Chain, item : ID - NULL | 
		c1 != c2 => {
			{
				Chain_Add[c1, item] 
				Chain_Remove[c2,item]

			} => Chain_Remove[c2,item]
		}
}


check {
	all c1,c2 : Chain, item : ID - NULL | 
		c1 != c2 => {
			{
				Chain_Add[c1, item] 
				Chain_Remove[c2,item]

			} => Chain_Add[c1,item]
		}
}
