# Scheduling an Apartment Viewing

I'm apartment hunting and trying to schedule a viewing at this place I found online. The landlord has a bunch of requirements I need to satisfy.

First up, timing. The landlord only does viewings on Saturday between 10am and 4pm. Each viewing takes 30 minutes. I can only make it between 1pm and 3pm because I've got errands in the morning.

Then there's the financial stuff. The apartment is $2400 per month. The landlord requires that your monthly income is at least 3 times the rent - so I'd need to be making at least $7200 per month. I make $8000 per month, so that part should be fine.

But wait, there's also the approved tenant list situation. The landlord uses a background check service and they maintain a pre-approved list. If you're on the pre-approved list, you can view any available time slot. If you're not on the list, you can only view slots after 2pm - basically the less desirable times. I checked and I'm not on their pre-approved list yet.

So we're combining temporal constraints (Saturday 10am-4pm overall window, my 1-3pm availability, 30-minute viewing duration), arithmetic constraints (rent $2400, income requirement 3x rent, my income $8000), and access control (pre-approved vs non-approved viewing slot restrictions).

Can I schedule a viewing that works with my schedule, meets the income requirements, and respects the approved tenant restrictions?

Logic: QF_IDL + QF_LIA + QF_UFLIA
