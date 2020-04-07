module monopoly

open util/ordering [State] as ord

sig State {}

sig Dice {}

 sig Player {	
	token: one Token, 
	money: set Money,
	ownedProperties: set Property,
	ownedUtilities: set Utilities,
	ownedRailroads: set Railroad,
	houses: Property -> House ,
	hotels: Property -> Hotel  
}

abstract sig Location extends Purchasable{
}

abstract sig Building extends Purchasable {
}

one sig Board{
	players: some Player,
	spaces: some Location
}

sig Token {}{
	 one this.~token
}

sig Money {}

abstract sig Purchasable{
	price: one Price
}

sig Price {}{
	one this.~price
}

sig Property extends Location{
	houses: set House,
	hotels: lone Hotel
}

sig Utilities extends Location{}
sig Railroad extends Location{}

sig Hotel extends Building {}
sig House extends Building {}

fact allPlayersOnBoard{
	all p: Player | one b:Board | p in b.players
}

fact allSpacesOnBoard{
	all l: Location | one b:Board | l in b.spaces
}

fact uniqueProperties { 
	no disj p, p': Player | p.ownedProperties = p'.ownedProperties
}

fact uniqueUtilities { 
	no disj p, p': Player | p.ownedUtilities = p'.ownedUtilities
}

fact uniqueRailroads { 
	no disj p, p': Player | p.ownedRailroads = p'.ownedRailroads
}

fact uniqueMoney { 
	no disj p, p': Player | p.money = p'.money
}

fact oneBalance { 
	all p: Player | one p.money 
}

fact needFourHouses { 
	all p: Player | #p.houses < 4 implies #p.hotels = 0
}

pred show (b: Board){
	#b.players > 1
}

run show
