module monopoly

open util/ordering [State] as ord

sig State {}

abstract sig Player {	
	token: one Token, 
	money: set Money,
	ownedProperties: some Property,
	ownedUtilities: some Utilities,
	ownedRailroads: some Railroad,
	houses: Property -> House,
	hotels: Property -> Hotel 
}

abstract sig Location{
	price: one Price
} {

}

abstract sig Building {
	price: one Price
}

one sig Board{
	players: some Player,
	spaces: some Location
}

fact allPlayersOnBoard{
	all p:Player | one b:Board | p in b.players
}

fact allSpacesOnBoard{
	all l:Location | one b:Board | l in b.spaces
}

fact locationPriceUnique{
	all l, l':Location | l.price = l'.price implies l = l'
}


sig Token {}{
     one this.~token
}
sig Money {}
sig Price {}

sig Property extends Location{
	houses: set House,
	hotels: lone Hotel
}

sig Utilities extends Location{}{
	one ~price
}
sig Railroad extends Location{}{
	one ~price
}


sig Hotel extends Building {}
sig House extends Building {}



run {}
