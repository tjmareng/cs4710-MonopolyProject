module monopoly

open util/ordering [State] as ord

// ----------------------- SIGNATURES ----------------------- //
sig State {}
sig Dice {}

// Board sig has Players and Spaces which are Locations
one sig Board{
	players: some Player,
	spaces: some Location
}

// Player sig
sig Player {	
	token: one Token, 
	money: set Money,
	ownedProperties: set Property,
	ownedUtilities: set Utilities,
	ownedRailroads: set Railroad,
	houses: Property -> House ,
	hotels: Property -> Hotel  
}

// Tokens are unique to each player
sig Token {}{ one this.~token }

// Abstract sig representing a purchasable signature
abstract sig Purchasable{ price: one Price }
abstract sig Location extends Purchasable{}
abstract sig Building extends Purchasable {}
sig Money {}

// Prices are unique
sig Price {}{ one this.~price }

// Property is a Location which can have Houses or up to one Hotel
sig Property extends Location{
	houses: set House,
	hotels: lone Hotel
}
sig Hotel extends Building {}
sig House extends Building {}

// Utilities and Railroads are Locations with a Price
sig Utilities extends Location{}
sig Railroad extends Location{}

// Die sig contains values to be rolled
//sig Die{ values: set Values }
//sig Values{}

// Each game has a Banker
//one sig Banker extends Player{}
// ----------------------- SIGNATURES ----------------------- //

// ----------------------- FACTS ----------------------- //
// If two Players have the same Properties, then they are the same Player
fact uniqueProperties { 
	no disj p, p': Player | p.ownedProperties = p'.ownedProperties
}

// If two Players have the same Utilities, then they are the same Player
fact uniqueUtilities { 
	no disj p, p': Player | p.ownedUtilities = p'.ownedUtilities
}

// If two Players have the same Railroads, then they are the same Player
fact uniqueRailroads { 
	no disj p, p': Player | p.ownedRailroads = p'.ownedRailroads
}

// If two Players have the same Money, then they are the same Player
fact uniqueMoney { 
	no disj p, p': Player | p.money = p'.money
}

// Players only have one money balance
fact oneBalance { 
	all p: Player | one p.money 
}

// A Player cannot have a Hotel without 4 Houses
fact needFourHouses { 
	all p: Player | #p.houses < 4 implies #p.hotels = 0
}

// Players are on the Board
fact allPlayersOnBoard{
	all p: Player | one b:Board | p in b.players
}

// Spaces are on the Board
fact allSpacesOnBoard{
	all l: Location | one b:Board | l in b.spaces
}
// ----------------------- FACTS ----------------------- //

// ----------------------- FUNCTIONS ----------------------- //
fun allOwnedLocations[b: Board] : set Location {
	b.players.(ownedRailroads + ownedUtilities + ownedProperties)
}
pred ownRailroad[b: Board, r: Railroad] {
	r in allOwnedLocations[b]
}
pred ownUtility[b: Board, u: Utilities] {
	u in allOwnedLocations[b]
}
pred ownProperty[b: Board, p: Property] {
	p in allOwnedLocations[b]
}
//run ownRailroad
//run ownUtility
run ownProperty

//fun lookUpHouses[p: Player, h: House] : set Player {
//	p.houses[h]
//}
//fun lookUpHotel[p: Player,  pr: Property] : set Hotel {
//	p.hotels[pr]
//}
// ----------------------- FUNCTIONS ----------------------- //

// ----------------------- ASSERTIONS ----------------------- //
// ----------------------- ASSERTIONS ----------------------- //

pred show (b: Board){
	#b.players > 1
}
run show
