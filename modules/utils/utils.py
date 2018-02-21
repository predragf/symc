import string
import random

def generateRandomLetterSequence(sequenceLength):
    return ''.join(random.choice(string.ascii_uppercase) for _ in range(sequenceLength))
