# TrackMe
<p align="center">
  <img width="100%" src="https://i.imgur.com/tm9mSuM.png" alt="header" />
</p>
<p align="center">
    <img src="https://i.imgur.com/mPb3Qbd.gif" width="180" alt="Politecnico di Milano"/>
</p>

## Description
This repo contains the deliverables for the "Software Engineering 2" course at Politecnico di Milano: a **RASD** (Requirements Analysis and Specification Document) and a **DD** (Design Document), written for a fake company (TrackMe) that wants a complex application to be designed and developed.

## The assignment
TrackMe is a company that wants to develop a software-based service allowing third-parties to monitor the location and health status of individuals. This service is called **Data4Help**. The service supports the registration of individuals who, by registering, agree that TrackMe acquires their data (through smartwatches or similar devices). Also, it supports the registration of third parties. After registration, these third parties can request:
- Access to the data of some specific individuals (we assume for instance that they know his/her fiscal code in Italy). In this case, TrackMe passes the request to the specific individual who can accept or refuse it.
- Access to anonymized data of group of individuals (for instance all those living in a certain geographical area). The requests are handled directly by TrackMe that approves them if it is able to properly anonymize the requested data. For instance, if the third party is asking for data about 10-year-old children living in a certain street in Milano and the number of these children is two, then the third party could be able to derive their identity simply having people monitoring the residents of the street between 8.00 and 9.00 when kids go to school. Then, to avoid this risk and the possibility of a misuse of data, TrackMe will not accept the request. For simplicity, we assume that TrackMe will accept any request for which the number of individuals whose data satisfy the request is higher than 1000.

As soon as a request for data is approved, TrackMe makes the previously saved data available to the third party. Also, it allows the third party to subscribe to new data and to receive them as soon as they are produced.

Imagine now that, after some time, TrackMe realizes that a good part of its third-party customers wants to use the data acquired through Data4Help to offer a personalized and non-intrusive SOS service to elderly people. Therefore, TrackMe decides to build a new service, called **AutomatedSOS**, on top of Data4Help. AutomatedSOS monitors the health status of the subscribed customers and, when such parameters are below certain thresholds, sends to the location of the customer an ambulance, guaranteeing a reaction time of less than 5 seconds from the time the parameters are below the threshold.

Finally, TrackMe realizes that another great source of revenues could be the development of a service to track athletes participating in a run. In this case, the service, called **Track4Run**, should allow organizers to define the path for the run, participants to enroll to the run, and spectators to see on a map the position of all runners during the run. Of course, also in this case, Track4Run will exploit the features offered by Data4Help.

## Group
| First name | Last Name | Email address   |
| ---------- | --------- | --------------- |
| Emilio | Imperiali | emilio.imperiali@mail.polimi.it |
| Giorgio | Labate | giorgio.labate@mail.polimi.it |
| Mattia | Mancassola  | mattia.mancassola@mail.polimi.it |
