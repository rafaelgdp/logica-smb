sig Mario {
	-- Item item
	Estado estado
}

sig SuperMario extends Mario {}
sig FireMario extends Mario {}
sig MarioCapa extends Mario {}
sig MarioMorto extends Mario {}
sig MarioInvencivel extends Mario {}

-- sig Item {}
-- sig ItemFlor extends Item {}


pred show[] {

}

run show for 3
