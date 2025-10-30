# Same-Day Shipping Guarantee Verification

This online store advertises a shipping guarantee that says if you place your order before noon (12:00 PM), they guarantee it ships out the same day. That's their promise to customers - ANY order placed before noon gets same-day shipping, period.

We've got their order fulfillment database with timestamps for when orders were placed and when they actually shipped. Here's what we see:
- Order 5001 placed at 9:30 AM, shipped at 2:15 PM same day
- Order 5002 placed at 11:45 AM, shipped at 3:00 PM same day
- Order 5003 placed at 10:15 AM, shipped at 1:30 PM same day
- Order 5004 placed at 8:00 AM, shipped at 11:45 AM same day
- Order 5005 placed at 11:59 AM, shipped at 4:30 PM same day
- Order 5006 placed at 7:30 AM, shipped at 10:00 AM same day
- Order 5007 placed at 10:45 AM, shipped at 2:45 PM same day
- Order 5008 placed at 9:00 AM, shipped at 1:15 PM same day

The universal guarantee claim is: for any order X, if the order placement time is before 12:00 PM (720 minutes after midnight), then the shipping time is on the same day as the order time.

We can see these specific orders and they all seem to follow the rule. But does the guarantee actually hold for EVERY order placed before noon? Not just these 8 examples, but for all morning orders throughout their entire operation?

This is tricky because we're verifying a conditional universal statement (if before noon, then same-day shipping) based on finite data points. The gap between "these examples work" and "the universal guarantee holds" is where things get complex.

Logic: UFLIA (with quantifiers)
