# ChatGPT usage monitor

A Tampermonkey userscript for `chatgpt.com/settings/usage`. It reads the weekly limit every few seconds, predicts when it will hit 0% from the 1% tick-overs, and alarms 24, 12 and 6 seconds before (plus a 90 s heads-up and a % backstop). It keeps every cycle, scores each alarm against the real run-out, and re-picks the burn curve and alarm timing after every cycle. It also shows what the burn costs: credit balance and burn, one allowance in credits versus a $125 instant reset, time to the free weekly reset, and today's resets and stall time.

**Install / update:** open the raw file in Chrome with Tampermonkey installed:

https://raw.githubusercontent.com/garitar/usage-monitor/main/chatgpt-usage-monitor.user.js

Every change raises `@version`; Tampermonkey updates from the same address, and the monitor shows an Update button when a newer build is here.
