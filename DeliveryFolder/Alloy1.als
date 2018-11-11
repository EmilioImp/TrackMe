sig FiscalCode{}
sig Username{}
sig Password{}
sig Registration{
	username: one Username,
	password: one Password
}
abstract sig Customer{
	registration: one Registration
}

sig User extends Customer{
	fiscalCode: one FiscalCode,
	healthStatus: one HealthStatus,
	location: one Location,
	emergencyCall: lone EmergencyCall,
	runsWatching: lone Run,
	runsEnrolledFor: set Run 
	--It may happen that a user enrolls for a run and then doesn’t participate to it and  
	--wants to follow it, for this reason it is NOT stated that ‘runsWatching’ and
--‘runsEnrolledFor’ are disjoint
}
sig ThirdParty extends Customer{
	organizedRuns: set Run,
	warningsReceived: set Warning,
	receivedEmergencyCalls: set EmergencyCall,
	subscriptedUsers: set User
}
sig Location{
	latitude: one Int,
	longitude: one Int
}

--{latitude >= -90 and latitude <= 90 and longitude >= -180 and longitude <= 180} 
--NB: scaled values for simplicity
{latitude >= -3 and latitude <= 3 and longitude >= -6 and longitude <= 6 }

sig HealthStatus{
	heartbeat: one Int,
	bodyTemperature: one Int
}

--{heartbeat >= 30 and heartbeat <= 210 and bodyTemperature >= 30 and bodyTemperature <= 45}
--NB: scaled values for simplicity
{heartbeat >= 3 and heartbeat <= 7 and bodyTemperature >= 3 and bodyTemperature <= 5}

--Contains HealthStatus and Location even if they could be retrieved from User
sig EmergencyCall{
	userToAssist: one User,
	userHealthStatus: one HealthStatus,
	userLocation: one Location
}

--The health status and location contained in the emergency call must be the health status and location of the user for 
--which is done
{userHealthStatus = userToAssist.healthStatus and userLocation = userToAssist.location}

abstract sig Warning{}

one sig RefuseWarning extends Warning{}

sig SingleRequest{
authorOfRequest: one ThirdParty,
subjectOfRequest: one User
}

--Represent the result of a single request and is associated to all the single requests that gave this result
abstract sig SingleRequestResult{
	request: set SingleRequest
}

one sig SingleRequestAccepted extends SingleRequestResult{}
one sig SingleRequestRefused extends SingleRequestResult{}
one sig PrivacyWarning extends Warning{}

sig AggregateRequest{
	matchingUsers: set User,
	authorOfRequest: one ThirdParty,
	privacyWarning: lone PrivacyWarning
}

--The request generates a warning if, and only if, the privacy cannot be guaranteed
--{#privacyWarning = 1 iff #matchingUsers < 1000}
--NB: scaled values for simplicity
{ #privacyWarning = 1 iff #matchingUsers < 5}

sig Path{}
sig Date{}
sig RunName{}

sig Run{
	name: one RunName,
	date: one Date,
	path: one Path,
	startingPoint: one Location,
	endingPoint: one Location	 
}

--All FiscalCodes have to be associated to a User
fact FiscalCodeUserConnection{
	all fc: FiscalCode | some u: User | fc in u.fiscalCode
}

--All Usernames have to be associated to a Registration
fact UsernameRegistrationConnection{
	all u: Username | some r: Registration | u in r.username
}

--All Passwords have to be associated to a Registration
fact PasswordRegistrationConnection{
	all p: Password | some r: Registration | p in r.password
}

fact RegistrationCustomerConnection {
	all r: Registration | some c: Customer | r in c.registration
}

--Every Customer has a unique username
fact NoSameUsername {
	no disj c1,c2: Customer | c1.registration.username = c2.registration.username
}

--Every User has a unique SSN
fact NoSameFiscalCode {
	no disj u1,u2 : User | u1.fiscalCode = u2.fiscalCode
}


--The third party is notified of the refusing if the request has not been accepted
fact RefuseWarningIfRefuse{
all sr: SingleRequest | one r: SingleRequestRefused | sr in r.request implies (RefuseWarning in sr.authorOfRequest.warningsReceived)
}

--The third party has made a request that has not been accepted if it has been notified with 
--the warning
fact RefuseWarningOnlyIfNeeded{
all tp: ThirdParty | RefuseWarning in tp.warningsReceived implies (some sr: SingleRequest | tp in sr.authorOfRequest and (one r: SingleRequestRefused | sr in r.request))
}

--Every single request can be either accepted or refused, not both.
fact SingleRequestAcceptedOrRefused{
all sr: SingleRequest | (some srr: SingleRequestResult | sr in srr.request) and (no disj srr1,srr2: SingleRequestResult | sr in srr1.request and sr in srr2.request)
}

--The third party is notified of the problem if the privacy cannot be guaranteed
--NB: scaled values for simplicity (the 5 should be 1000)
fact NotMoreThan1000MatchingUsers{
all ar: AggregateRequest | #ar.matchingUsers < 5 implies (PrivacyWarning in ar.authorOfRequest.warningsReceived) 
}

--The privacy cannot be guaranteed if the third party is notified 
--NB: scaled values for simplicity (the 5 should be 1000)
fact PrivacyWarningOnlyIfNeeded{
all tp: ThirdParty | PrivacyWarning in tp.warningsReceived implies (some ar: AggregateRequest | tp in ar.authorOfRequest and #ar.matchingUsers < 5)
}

--The emergency call is created if, and only if, the user needs it (his parameters are out of bounds)
fact EmergencyCallIfAndOnlyIfNeeded{
	all u: User | (
(#u.emergencyCall = 1) iff (u.healthStatus.heartbeat <= 4 or u.healthStatus.heartbeat >= 6 or u.healthStatus.bodyTemperature <= 3 or u.healthStatus.bodyTemperature >= 5)
)
}

--All Health Status have to be associated to a User
--NB: two users CAN have the same health status
fact HealthStatusUserConnection {
	all hs: HealthStatus | some u: User | (u.healthStatus = hs) 
}

--All present Emergency Calls have to be associated to a User (the reference is mutual) and to a thirdParty
--NB: the emergency has to be received only from one third party
fact EmergencyCallConnection {
	all u: User, ec: EmergencyCall | (ec.userToAssist = u iff u.emergencyCall = ec)
            	and (one tp: ThirdParty | ec in tp.receivedEmergencyCalls)   	
}

--All Paths have to be associated to a Run
fact PathRunConnection{
	all p: Path | some r: Run | p in r.path
}

--All Dates have to be associated to a Run
fact DateRunConnection{
	all d: Date | some r: Run | d in r.date
}
--There can’t be two runs with the same name and with the same date
fact NoRunsWithSameNameAndDate{
	no disj r1,r2: Run | r1.name = r2.name and r1.date = r2.date
}
--All Locations have to be associated to a User or to a Run
fact LocationConnection{
	all loc: Location | (some u:User | loc in u.location) or (some r: Run | loc in r.startingPoint or loc in r.endingPoint) 
}

--All runs are organized by one and only one third party
fact RunThirdPartyConnection {
all r: Run | one tp: ThirdParty | r in tp.organizedRuns
}

---------------------------------------------------------------------------------------------------------------------------

assert NoDifferentThirdPartiesReceivingTheSameEmergencyCall{
no disj tp1, tp2: ThirdParty | some ec: EmergencyCall | ec in tp1.receivedEmergencyCalls and ec in tp2.receivedEmergencyCalls
}

assert AggregateRequestHasWarningCorrectly {
	all ar: AggregateRequest | #ar.matchingUsers >= 5 iff #ar.privacyWarning = 0
}

assert NoSingleRequestBothAcceptedAndRefused{
no sr: SingleRequest | (one a: SingleRequestAccepted | sr in a.request) and (one r: SingleRequestRefused | sr in r.request)
}

check NoDifferentThirdPartiesReceivingTheSameEmergencyCall for 3

check AggregateRequestHasWarningCorrectly for 5

check NoSingleRequestBothAcceptedAndRefused for 5
--------------------------------------------------------------------------------------------------------------------
pred world1 {
	#SingleRequest = 2
	#SingleRequestAccepted.request = 1
	#SingleRequestRefused.request = 1
	#ThirdParty = 2 
(some disj t1, t2: ThirdParty | some disj s1, s2: SingleRequest  | t1 in s1.authorOfRequest and t2 in s2.authorOfRequest and s1 in SingleRequestAccepted.request and s2 in SingleRequestRefused.request)
}

run world1 for 4 but 0 Run, 0 EmergencyCall, 0 AggregateRequest

pred world2{
#AggregateRequest = 2
    	#User = 5
    	#ThirdParty = 2	
(some disj a1,a2: AggregateRequest | a1.authorOfRequest != a2.authorOfRequest and #a1.matchingUsers = 5 and  #a2.matchingUsers = 2)
}

run world2 for 7 but 0 Run, 0 EmergencyCall, 0 SingleRequest

pred world3 {
	#ThirdParty = 1
	#User = 1
	#EmergencyCall = 1
(some u:User | some tp:ThirdParty | some ec:EmergencyCall | ec.userToAssist = u and u.emergencyCall = ec and ec in tp.receivedEmergencyCalls)
}

run world3 for 2 but 0 Run, 0 SingleRequest
pred world4{
	 #Run = 2
}

run world4 for 2 but 0 EmergencyCall, 0 SingleRequest, 0 AggregateRequest
