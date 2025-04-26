
open id
open Set
open Chain

pred retrieve[s :Set, c : Chain]
{
	Set_items[s] = Chain_items[c]
}

// retrieve is functional from chains to sets

check {
	all s1, s2 : Set, c : Chain | 
		{ 
			retrieve[s1,c]
			retrieve[s2,c]
		}
		=>
		{
			Set_items[s1] = Set_items[s2]
		}
}

// Set_Add simulates Chain_Add

check {
	all s : Set , c : Chain , item : ID - NULL |
		{
			{ 
				Set_Inv[s]
				Chain_Inv[c]
				retrieve[s,c]
				after (retrieve[s,c])
				Chain_Add[c,item]
			}
			=> 
			{
				Set_Add[s,item]
			}
		}		
} for 4 but exactly 1 Set ,exactly 1 Chain

// Set_Remove simulates Chain_Remove

check {
	all s : Set , c : Chain , item : ID - NULL |
		{
			{ 
				Set_Inv[s]
				Chain_Inv[c]
				retrieve[s,c]
				after (retrieve[s,c])
				Chain_Remove[c,item]
			}
			=> 
			{
				Set_Remove[s,item]
			}
		}		
} for 4 but exactly 1 Set ,exactly 1 Chain

// example to illustrate how set_add simulates chain_add

run
{
	some s:Set ,c :Chain , item : ID - NULL |
	{ 
		Set_Inv[s]
		Chain_Inv[c]
		retrieve[s,c]
		after (retrieve[s,c])
		Chain_Add[c,item]
		Set_Add[s,item]
	}
} for 4 but exactly 1 Set ,exactly 1 Chain
		
			
