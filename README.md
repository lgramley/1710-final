# 1710-final

What tradeoffs did you make in choosing your representation? What else did you try that didn’t work as well?

- Board vs storing location in the sig
- passing in passengers and focusing on passenger specific requests rather than from a master request list.
- we focused only on drivers and passengers, did not include any stakeholders beyond that. 


What assumptions did you make about scope? What are the limits of your model?

- We assumed that if we got it working for one driver and one passenger that it would be easily expandable to multiple drivers and multiple passengers but that just was not true. We overconstrained the model to work with the first scenario we tried. The model works with an even number of passengers and drivers but not beyond that. We have an attempt that overconstraints to work with 1 driver and 2 passengers but it only happens to work in that case.


Did your goals change at all from your proposal? Did you realize anything you planned was unrealistic, or that anything you thought was unrealistic was doable?

- Yes our goals drastically changed from our proposal. There was an additional layer of complication as we went for a two axis grid instead of using a number line like we additionally thought. Planning for a mismatched number of drivers and passengers was unrealistic, cancelling requests after they've been accepted was unrealistic, the rideshare option would've been hard to achieve with the base assumptions we made, and ratings seemed irrelevant for our base goals.
- Our goals shifted to ensuring that requests worked and that you can claim and fulfill requests in a manner specified by different procedures. We prioritized getting it to work so we can attempt different procedures.


How should we understand an instance of your model and what your visualization shows (whether custom or default)?

- In order to understand our model there are a few things you should focus on:
    -for movement you should look at location_x and location_y for the drivers and locationx and locationy for the passengers
    -for requests you should look at the claimed and fulfilled fields, the claimed field change should change to one when it gets added to the driver's accepted_requests set