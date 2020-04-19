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
some sig Player {	
	token: one Token, 
	money: set Money,
	ownedProperties: one OwnedProperties,
	ownedUtilities: one OwnedUtilities,
	ownedRailroads: one OwnedRailroads,
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
sig OwnedProperties { 
	properties: set Property,
 	houses: Property->House,
	hotels: Property->Hotel
}
sig Property extends Location{
	houses: set House,
	hotels: lone Hotel
}
sig Hotel extends Building {}
sig House extends Building {}

// Utilities and Railroads are Locations with a Price
sig OwnedUtilities { utilities: set Utilities }
sig Utilities extends Location{}
sig OwnedRailroads { railroads: set Railroad }
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

// Players only have one money balance
fact oneSetofProperties { 
	all p: Player | one p.ownedProperties
}

// A Player cannot have a Hotel without 4 Houses
fact needFourHouses { 
//	all p: Player | #p.houses < 4 implies #p.hotels = 0
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
	b.players.ownedProperties.properties + b.players.ownedUtilities.utilities + b.players.ownedRailroads.railroads
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
//run ownProperty

fun lookUpHouses[p: Player, pr: Property] : set House {
	p.ownedProperties.houses[pr]
}
fact everyHouseMapped {
	all p: Player, pr: Property | some p.ownedProperties.houses implies some lookUpHouses[p, pr]
}

fun lookUpHotels[p: Player, pr: Property] : set Hotel {
	p.ownedProperties.hotels[pr]
}
fact everyHotelMapped {
	all p: Player, pr: Property | some p.ownedProperties.hotels implies some lookUpHotels[p, pr]
}
// ----------------------- FUNCTIONS ----------------------- //

// ----------------------- ASSERTIONS ----------------------- //
//Checks that there is in fact only one board
assert oneBoard {
	
}

//Checks that all players have a token
assert playerHasAToken {
	
}

//Checks that all players start with one money stack
assert playerHasOneMoneyStack {
	
}

//Checks that all players start with no locations
assert PlayerHasNoLocations {
	
}

// ----------------------- ASSERTIONS ----------------------- //

pred show (b: Board, o: OwnedProperties){
	#b.players > 1
	#o.properties > 1
	
}
run show
