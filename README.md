# 1710-final

Video: https://drive.google.com/file/d/1M_pWcPSV7zvX97RzawNjVwZaAwT6lbMp/view?usp=sharing

What tradeoffs did you make in choosing your representation? What else did you try that didn’t work as well?

- We initially approached the assignment with a more object-oriented mindset 
creating sigs for Boards and Tiles. We eventually realized that this would be 
drastically increase the load on Forge as it would have to configure multiple 
combinations of tiles, for example, so we decided to simply store locations as 
coordinates in the Passenger and Driver sig. Similarly, we initially had a Car 
sig that we took out because it was irrelevant as Drivers can easily symbolize cars.

- We initially wanted to model requests as being one large master list, and 
drivers could accept depending on factors like capacity, location, etc. 
As we were simplifying our model into the main Driver and Passenger sigs,
we decided to make Requests and Passengers more intertwined, so our mechanism 
for accepting requests is without the master list. As we ran into issues later,
we realized that perhaps a master list would have been more successful to help 
accommodate for multiple passengers. 

- We focused only on drivers and passengers, did not include any stakeholders 
beyond that. We were able to include all of the components we found relevant 
in just these two stake holders which are represented in their
repspective sigs. 


What assumptions did you make about scope? What are the limits of your model?


- We assumed that if we got it working for one driver and one passenger that it 
would be easily expandable to multiple drivers and multiple passengers but that 
proved to be false. We overconstrained the model to work with the first scenario 
we tried. The model works with an even number of passengers and drivers but not 
beyond that. We have an attempt that overconstraints to work with 1 driver and 2 
passengers but it only happens to work in that case.


Did your goals change at all from your proposal? Did you realize anything you planned was unrealistic, or that anything you thought was unrealistic was doable?


- Yes our goals drastically changed from our proposal. There was an additional 
layer of complication as we went for a two axis grid instead of using a number 
line like we additionally thought. Planning for a mismatched number of drivers 
and passengers was unrealistic because it turned out to be much more complicated 
to have one driver accept and complete one request before taking on another. This 
was because of the way our different action choices were configured in our traces, 
and it was possible for a given passenger to not follow constraints because the 
predicates didn't apply to that *specific* passenger, or it would be unsat.

- To follow the conceptual model of rideshare models, we also wanted to implement 
passengers cancelling requests, but we realized that was not within our scope and 
not super relevant to our overall goals like we intially thought. Similarly, 
having a rideshare option in which some passengers could opt for rideshare and 
others could not would have been difficult to achieve. However, the model does 
somewhat inherently handle this as we do account for party size. Addint a ratings 
field also seemed irrelevant for our goals however should we wanted to implement 
we could have just added it to our sigs. 

- Our goals shifted to ensuring that requests worked and that you can claim and
fulfill requests in a manner specified by different procedures. We prioritized 
getting it to work so we can attempt different procedures.

- Despite these challenges, our model certainly has some benefits even if they 
are not totally applicable to real world systems. For example, a balanced number 
of passengers and drivers ensures that all passengers get picked up and dropped 
off at their destination in a timely manner (which is of course their main concern) 
and it ensures that all drivers can find a passenger to pick up (which is in their 
best interest as a driver).


How you structured your model and what you proved?

We had 3 main sigs: Driver, Passenger, Request. Drivers and passengers know their 
own location and passengers contain a request. Requests contain an origin and 
destination, as well as field for claimed and fulfilled
in a given state. Drivers can do any number of actions, including moving, claiming, 
picking up, and dropping off.
Drivers will accept requests, then drive towards the location of the passenger, 
pick them up, drive to the destination, and then drop them off. Passengers are 
completely passive: they do not move unless picked up, and then do not move after 
they are dropped off. However, they do of course move with/at the same time as the 
car which we built into our move predicates. Our procedures are discussed later 
but they mainly specifiy the path in which the Driver can move with and without the passenger.


How should we understand an instance of your model and what your visualization shows (whether custom or default)?
- We used the default visualizer and specifically found the table setting to me the most clear/helpful
- In order to understand our model there are a few things you should focus on:
    - for movement you should look at location_x and location_y for the drivers and 
    locationx and locationy for the passengers. You can see that once a driver picks 
    up a passenger, they move together. You can also notice the use of the destination 
    and origin fields that ensure a passenger gets picked up by a driver at 
    their specificed origin and dropped off at their specified destination.
    - for requests you should look at the claimed and fulfilled fields, the claimed 
    field change should change to one when it gets added to the driver's 
    accepted_requests set. This can (and realisticly should) happen before the 
    driver reaches the passengers (just as it does in rideshare apps). 


Properties and Stakeholders:

Our properties are mostly focused on the movement of the drivers/cars. 
Procedures 1-3 focus more on the route while 4-5 focus on the claiming logic.
We state the directions in which the cars should move to pick up or drop off a 
passenger. In some cases this may be beneficial to the driver. For example, not 
having to turn around ensures an easier route. Or as another example, not being 
able to claim a passenger until you are within a block of them reduces the chance 
of the passenger cancelling a ride. On the passenger side of things, not being 
claimed until the driver is close may help with wait times when there are a lot 
of drivers and also may ensure a driver is less likley to cancel on a passenger. 
Having used rideshare apps, we have had rides cancelled on us because they arrive 
and cannot find us or they arrive and see a wait time they were not expecting 
(for example a concert or sporting event where all the cars leave at once). I 
think it is important to consider the main considerations of our two major stake 
holders. Drivers obviously value passengers that will not cancel and passengers 
that are on their way/in their path already for convience sake. Passengers value 
low wait times and efficient drivers as well as drivers who will not cancel. 
 
What we proved/learned?
- There is a very complex relationship between modeling many aspects of different systems, especially this one. Additionally, scale complexities are a very important factor. 
- Our model proved the complexity of rideshare apps 
- Each driver and passenger is an independent entity that can do any number of 
actions regardless of what other drivers or passengers are doing. Fully 
encapsulating this idea in forge is unrealistic due to the sheer number of 
possibilities at any given moment. Not only do passengers need to move from 
their origin to their destination, but a specific driver needs to pick them up 
and drop them off, and it must also be the case that each passenger only gets 
claimed by one driver in a given moment.
Lastly, we also learned that although we did a substantial amount of planning, 
we should still always be thinking many steps ahead when implementing a model 
as each guard, rule, and predicate will effect something else. 

We did not collaborate with other classmates on this project. We sought help 
from Tim and our mentor TA at our meetings. We did most of this together though 
which was helpful for us to bounce ideas off one another and discuss as we 
designed and implemented. 